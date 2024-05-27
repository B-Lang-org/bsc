#include <vector>
#include <cstdio>

#include "event_queue.h"

/* we need these for the debugging routines only */
#include "priority.h"
extern "C" const char* bk_clock_name(tSimStateHdl simHdl, tClock handle);


/* Fundamental heap operations */

#define PARENT(n) ((n-1)/2)
#define LEFT(n)   ((2*n)+1)
#define RIGHT(n)  ((2*n)+2)

/* Comparison function for ordering events */
bool operator<(const tEvent& e1, const tEvent& e2)
{
  if (e1.at < e2.at)
    return true;
  else if (e1.at > e2.at)
    return false;
  else
    return (e1.priority < e2.priority);
}

/* Move an element in the heap up until
 * the heap property is restored.
 */
void EventQueue::bubble_up(unsigned int idx)
{
  unsigned int current = idx;
  unsigned int parent = PARENT(current);

  while ((current != 0) && (events[current] < events[parent]))
  {
    std::swap<tEvent>(events[current],events[parent]);
    current = parent;
    parent = PARENT(current);
  }
}

/* Move an element in the heap down until
 * the heap property is restored.
 */
void EventQueue::bubble_down(unsigned int idx)
{
  unsigned int parent = idx;
  unsigned int left;
  unsigned int right;

  while (true)
  {
    left  = LEFT(parent);
    right = RIGHT(parent);

    // find which node is the smallest out of parent and both children
    unsigned int smallest = parent;
    if ((right < count) && (events[right] < events[smallest]))
      smallest = right;
    if ((left < count) && (events[left] < events[smallest]))
      smallest = left;

    if (smallest == parent)
    {
      // we can stop bubbling down now -- the heap property holds
      return;
    }
    else
    {
      // we must swap with the smallest child and continue the loop
      std::swap<tEvent>(events[parent],events[smallest]);
      parent = smallest;
    }
  }
}

/* Check if the heap property holds */
bool EventQueue::isValid()
{
  for (unsigned int i = 0; i < count; ++i)
  {
    unsigned int l = LEFT(i);
    unsigned int r = RIGHT(i);
    if ((l < count) && (events[l] < events[i]))
      return false;
    if ((r < count) && (events[r] < events[i]))
      return false;
  }
  return true;
}

/*
 * The event queue operations
 */

/* Construct an EventQueue */
EventQueue::EventQueue()
  : events(), count(0), in_event(false), last_find_pred(NULL), curr_find_idx(0)
{}

/* Destroy an EventQueue and free its memory. */
EventQueue::~EventQueue()
{}

/* Add an event to the queue */
void EventQueue::schedule(const tEvent& e)
{
  if (count == events.size())
    events.push_back(e);
  else
    events[count] = e;
  bubble_up(count++);
}

/* Execute events in sequence */
void EventQueue::execute(tSimStateHdl simHdl)
{
  while (count > 0)
  {
    // We must copy the event rather than passing a reference
    // to the first event on the queue, since the event function
    // may schedule additional events and modify the queue.
    executing_event = events[0];

    // Remove the event from the queue
    if (--count > 0)
    {
      events[0] = events[count];
      bubble_down(0);
    }

    // Execute the event fn, passing in the copy of the event struct
    removed_self = false;
    in_event = true;
    tTime t = executing_event.fn(simHdl, executing_event);
    in_event = false;

    // If the event fn returned a non-zero time and did not
    // remove itself, then reschedule the event for that number
    // of time units in the future.
    if ((t != 0llu) && !removed_self)
    {
      executing_event.at += t;
      schedule(executing_event);
    }
  }
}

/* Get the number of events in the queue */
unsigned int EventQueue::size() const
{
  return count;
}

/* Search the queue for a matching event.
 * When a match is found, a pointer to the event is returned.
 * When there is no match, a NULL pointer is returned.
 * The search starts from the beginning when a predicate is
 * provided, and continues from the point of the last match
 * when the predicate is NULL.
 */
const tEvent* EventQueue::find(tSimStateHdl simHdl, tEventPredicate pred) const
{
  if (pred != NULL)
  {
    // start a new search
    last_find_pred = pred;
    curr_find_idx = 0;
  }

  if (last_find_pred != NULL)
  {
    const tEvent* ptr = NULL;
    while (curr_find_idx < count)
    {
      if (last_find_pred(simHdl, events[curr_find_idx]))
	ptr = &(events[curr_find_idx]);
      ++curr_find_idx;
      if (ptr)
	return (ptr);
    }
  }

  return NULL;
}

/* remove all events satisfying a predicate */
void EventQueue::remove(tSimStateHdl simHdl, tEventPredicate pred)
{
  if (pred == NULL)
    return;

  if (in_event)
    removed_self = pred(simHdl, executing_event);

  unsigned int i = 0;
  while (i < count)
  {
    if (pred(simHdl, events[i]))
    { // remove this event
      if (--count > 0)
      {
        events[i] = events[count];
	bubble_down(i);
        bubble_up(i);
      }
    }
    else
    { // keep this one
      ++i;
    }
  }
}

/* Remove all events */
void EventQueue::clear()
{
  events.clear();
  count = 0;
}

/* Print the event queue contents (for debugging) */
void EventQueue::print(tSimStateHdl simHdl) const
{
  printf("Event queue:\n");
  for (unsigned int i = 0; i < count; ++i)
  {
    printf("  %p(%p) @ %llu %s %s %s\n",
	   events[i].fn, events[i].data.ptr, events[i].at,
	   priority_group_name(priority_group(events[i].priority)),
	   priority_slot_name(priority_slot(events[i].priority)),
	   bk_clock_name(simHdl, priority_clock(events[i].priority)));
  }
}
