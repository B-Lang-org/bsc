#include <cstring>

#include "bs_target.h"

// FileTarget implementation simply forwards output to a file

FileTarget::FileTarget(FILE* file_ptr)
  : out(file_ptr)
{
  setlinebuf(file_ptr);
}

FileTarget::~FileTarget()
{
}

void FileTarget::write_char(char c)
{
  fputc(c, out);
}

void FileTarget::write_char(char c, unsigned int count)
{
  while (count-- > 0) fputc(c, out);
}

void FileTarget::write_string(const char* fmt ...)
{
  va_list ap;
  va_start(ap,fmt);
  vfprintf(out,fmt,ap);
  va_end(ap);
}

void FileTarget::write_data(const void* data,
			    unsigned int size, unsigned int num)
{
  if (fwrite(data,size,num,out) != num)
    perror("FileTarget::write_data");
}

// Buffer target stores output in a fixed-size buffer.
// It is constructed to mimic Verilog assignment rules in which
// assigning a string to a buffer which is too small truncates
// the string by removing leading characters.  We achieve this
// efficiently by treating the target as a circular buffer.

BufferTarget::BufferTarget(unsigned int size)
{
  // the buffer contains one extra space for the null terminator.
  buf_size = size + 1;
  buffer = new char[buf_size];
  start = 0;
  end = 0;
  buffer[end] = '\0';
}

BufferTarget::~BufferTarget()
{
  delete[] buffer;
}

void BufferTarget::write_char(char c)
{
  // overwrite the null terminator and move the terminator
  // forward one space (possibly overwriting the beginning of
  // the string).
  buffer[end++] = c;
  if (end == buf_size) end = 0;
  if (end == start) start = (start + 1) % buf_size;
  buffer[end] = '\0';
}

void BufferTarget::write_char(char c, unsigned int count)
{
  // write 'count' copies of 'c', add a null terminator
  // and adjust the start and end index values.
  unsigned int bytes = std::min(count, (buf_size-1));
  unsigned int back_bytes = std::min(bytes, (buf_size-end+1));
  unsigned int wrapped_bytes = bytes - back_bytes;
  unsigned int freespace = buf_size - 1 - length();
  if (back_bytes > 0)
    memset(buffer + end, c, back_bytes);
  if (wrapped_bytes > 0)
    memset(buffer, c, wrapped_bytes);
  end = (end + bytes) % buf_size;
  if (bytes > freespace)
    start = (start + bytes - freespace) % buf_size;
  buffer[end] = '\0';
}

void BufferTarget::write_string(const char* fmt ...)
{
  // not implemented for BufferTarget
}

void BufferTarget::write_data(const void* data,
			      unsigned int size, unsigned int num)
{
  // write size * num bytes of data, add a null terminator
  // and adjust the start and end index values.
  unsigned int bytes = std::min(size*num, (buf_size-1));
  unsigned int lost  = (size*num) - bytes;
  unsigned int back_bytes = std::min(bytes, (buf_size-end+1));
  unsigned int wrapped_bytes = bytes - back_bytes;
  unsigned int freespace = buf_size - 1 - length();
  const char* ptr = (const char*) data;
  if (back_bytes > 0)
    memmove(buffer + end, ptr + lost, back_bytes);
  if (wrapped_bytes > 0)
    memmove(buffer, ptr + lost + back_bytes, wrapped_bytes);
  end = (end + bytes) % buf_size;
  if (bytes > freespace)
    start = (start + bytes - freespace) % buf_size;
  buffer[end] = '\0';
}

const char* BufferTarget::str()
{
  // Fix up circular buffer so that string is contiguous.
  // This is an in-place permutation of the string.
  unsigned int len = length();
  unsigned int base = 0;
  unsigned int lo   = start;
  unsigned int hi   = buf_size-1;

  while (base != lo)
  {
    unsigned int in_order = 1 + hi - lo;
    unsigned int out_of_order = lo - base;
    unsigned int n = (out_of_order < in_order) ? out_of_order : in_order;

    for (unsigned int i = 0; i < n; ++i)
    {
      char tmp = buffer[base + i];
      buffer[base + i] = buffer[lo + i];
      buffer[lo + i] = tmp;
    }

    base += n;
    if (n != in_order)
      lo += n;
  }

  start = 0;
  end   = len;
  return buffer;
}

unsigned int BufferTarget::length() const
{
  if (end >= start)
    return (end - start);
  else
    return (end + buf_size - start);
}
