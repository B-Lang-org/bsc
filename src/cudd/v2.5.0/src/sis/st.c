/*
 * Revision Control Information
 *
 * /projects/hsis/CVS/utilities/st/st.c,v
 * serdar
 * 1.1
 * 1993/07/29 01:00:13
 *
 */
#include <stdio.h>
#include "util.h"
#include "st.h"

#define ST_NUMCMP(x,y) ((x) != (y))
#define ST_NUMHASH(x,size) (ABS((long)x)%(size))
#define ST_PTRHASH(x,size) ((int)((unsigned long)(x)>>2)%size)
#define EQUAL(func, x, y) \
    ((((func) == st_numcmp) || ((func) == st_ptrcmp)) ?\
      (ST_NUMCMP((x),(y)) == 0) : ((*func)((x), (y)) == 0))


#define do_hash(key, table)\
    ((int)((table->hash == st_ptrhash) ? ST_PTRHASH((key),(table)->num_bins) :\
     (table->hash == st_numhash) ? ST_NUMHASH((key), (table)->num_bins) :\
     (*table->hash)((key), (table)->num_bins)))

static int rehash (st_table *);

st_table *
st_init_table_with_params(
  ST_PFICPCP compare,
  ST_PFICPI hash,
  int size,
  int density,
  double grow_factor,
  int reorder_flag)
{
    int i;
    st_table *newt;

    newt = ALLOC(st_table, 1);
    if (newt == NIL(st_table)) {
	return NIL(st_table);
    }
    newt->compare = (int (*)(const char *, const char *)) compare;
    newt->hash = (int (*)(char *, int)) hash;
    newt->num_entries = 0;
    newt->max_density = density;
    newt->grow_factor = grow_factor;
    newt->reorder_flag = reorder_flag;
    if (size <= 0) {
	size = 1;
    }
    newt->num_bins = size;
    newt->bins = ALLOC(st_table_entry *, size);
    if (newt->bins == NIL(st_table_entry *)) {
	FREE(newt);
	return NIL(st_table);
    }
    for(i = 0; i < size; i++) {
	newt->bins[i] = 0;
    }
    return newt;
}

st_table *
st_init_table(ST_PFICPCP compare, ST_PFICPI hash)
{
    return st_init_table_with_params(compare, hash, ST_DEFAULT_INIT_TABLE_SIZE,
				     ST_DEFAULT_MAX_DENSITY,
				     ST_DEFAULT_GROW_FACTOR,
				     ST_DEFAULT_REORDER_FLAG);
}
			    
void
st_free_table(st_table *table)
{
    register st_table_entry *ptr, *next;
    int i;

    for(i = 0; i < table->num_bins ; i++) {
	ptr = table->bins[i];
	while (ptr != NIL(st_table_entry)) {
	    next = ptr->next;
	    FREE(ptr);
	    ptr = next;
	}
    }
    FREE(table->bins);
    FREE(table);
}

#define PTR_NOT_EQUAL(table, ptr, user_key)\
(ptr != NULL && !EQUAL(table->compare, user_key, (ptr)->key))

#define FIND_ENTRY(table, hash_val, key, ptr, last) \
    (last) = &(table)->bins[hash_val];\
    (ptr) = *(last);\
    while (PTR_NOT_EQUAL((table), (ptr), (key))) {\
	(last) = &(ptr)->next; (ptr) = *(last);\
    }\
    if ((ptr) != NULL && (table)->reorder_flag) {\
	*(last) = (ptr)->next;\
	(ptr)->next = (table)->bins[hash_val];\
	(table)->bins[hash_val] = (ptr);\
    }

int
st_lookup(st_table *table, char *key, char **value)
{
    int hash_val;
    register st_table_entry *ptr, **last;

    hash_val = do_hash(key, table);

    FIND_ENTRY(table, hash_val, key, ptr, last);
    
    if (ptr == NIL(st_table_entry)) {
	return 0;
    } else {
	if (value != NIL(char *)) {
	    *value = ptr->record; 
	}
	return 1;
    }
}

int
st_lookup_int(st_table *table, char *key, int *value)
{
    int hash_val;
    register st_table_entry *ptr, **last;

    hash_val = do_hash(key, table);

    FIND_ENTRY(table, hash_val, key, ptr, last);
    
    if (ptr == NIL(st_table_entry)) {
	return 0;
    } else {
	if (value != NIL(int)) {
	    *value = (int) (util_ptrint) ptr->record;
	}
	return 1;
    }
}

/* This macro does not check if memory allocation fails. Use at you own risk */
#define ADD_DIRECT(table, key, value, hash_val, newt)\
{\
    if (table->num_entries/table->num_bins >= table->max_density) {\
	rehash(table);\
	hash_val = do_hash(key,table);\
    }\
    \
    newt = ALLOC(st_table_entry, 1);\
    \
    newt->key = key;\
    newt->record = value;\
    newt->next = table->bins[hash_val];\
    table->bins[hash_val] = newt;\
    table->num_entries++;\
}

int
st_insert(st_table *table, char *key, char *value)
{
    int hash_val;
    st_table_entry *newt;
    register st_table_entry *ptr, **last;

    hash_val = do_hash(key, table);

    FIND_ENTRY(table, hash_val, key, ptr, last);

    if (ptr == NIL(st_table_entry)) {
	if (table->num_entries/table->num_bins >= table->max_density) {
	    if (rehash(table) == ST_OUT_OF_MEM) {
		return ST_OUT_OF_MEM;
	    }
	    hash_val = do_hash(key, table);
	}
	newt = ALLOC(st_table_entry, 1);
	if (newt == NIL(st_table_entry)) {
	    return ST_OUT_OF_MEM;
	}
	newt->key = key;
	newt->record = value;
	newt->next = table->bins[hash_val];
	table->bins[hash_val] = newt;
	table->num_entries++;
	return 0;
    } else {
	ptr->record = value;
	return 1;
    }
}

int
st_add_direct(st_table *table, char *key, char *value)
{
    int hash_val;
    st_table_entry *newt;
    
    hash_val = do_hash(key, table);
    if (table->num_entries / table->num_bins >= table->max_density) {
	if (rehash(table) == ST_OUT_OF_MEM) {
	    return ST_OUT_OF_MEM;
	}
    }
    hash_val = do_hash(key, table);
    newt = ALLOC(st_table_entry, 1);
    if (newt == NIL(st_table_entry)) {
	return ST_OUT_OF_MEM;
    }
    newt->key = key;
    newt->record = value;
    newt->next = table->bins[hash_val];
    table->bins[hash_val] = newt;
    table->num_entries++;
    return 1;
}

int
st_find_or_add(st_table *table, char *key, char ***slot)
{
    int hash_val;
    st_table_entry *newt, *ptr, **last;

    hash_val = do_hash(key, table);

    FIND_ENTRY(table, hash_val, key, ptr, last);

    if (ptr == NIL(st_table_entry)) {
	if (table->num_entries / table->num_bins >= table->max_density) {
	    if (rehash(table) == ST_OUT_OF_MEM) {
		return ST_OUT_OF_MEM;
	    }
	    hash_val = do_hash(key, table);
	}
	newt = ALLOC(st_table_entry, 1);
	if (newt == NIL(st_table_entry)) {
	    return ST_OUT_OF_MEM;
	}
	newt->key = key;
	newt->record = (char *) 0;
	newt->next = table->bins[hash_val];
	table->bins[hash_val] = newt;
	table->num_entries++;
	if (slot != NIL(char **)) *slot = &newt->record;
	return 0;
    } else {
	if (slot != NIL(char **)) *slot = &ptr->record;
	return 1;
    }
}

int
st_find(st_table *table, char *key, char ***slot)
{
    int hash_val;
    st_table_entry *ptr, **last;

    hash_val = do_hash(key, table);

    FIND_ENTRY(table, hash_val, key, ptr, last);

    if (ptr == NIL(st_table_entry)) {
	return 0;
    } else {
	if (slot != NIL(char **)) {
	    *slot = &ptr->record;
	}
	return 1;
    }
}

static int
rehash(st_table *table)
{
    register st_table_entry *ptr, *next, **old_bins;
    int             i, old_num_bins, hash_val, old_num_entries;

    /* save old values */
    old_bins = table->bins;
    old_num_bins = table->num_bins;
    old_num_entries = table->num_entries;

    /* rehash */
    table->num_bins = (int) (table->grow_factor * old_num_bins);
    if (table->num_bins % 2 == 0) {
	table->num_bins += 1;
    }
    table->num_entries = 0;
    table->bins = ALLOC(st_table_entry *, table->num_bins);
    if (table->bins == NIL(st_table_entry *)) {
	table->bins = old_bins;
	table->num_bins = old_num_bins;
	table->num_entries = old_num_entries;
	return ST_OUT_OF_MEM;
    }
    /* initialize */
    for (i = 0; i < table->num_bins; i++) {
	table->bins[i] = 0;
    }

    /* copy data over */
    for (i = 0; i < old_num_bins; i++) {
	ptr = old_bins[i];
	while (ptr != NIL(st_table_entry)) {
	    next = ptr->next;
	    hash_val = do_hash(ptr->key, table);
	    ptr->next = table->bins[hash_val];
	    table->bins[hash_val] = ptr;
	    table->num_entries++;
	    ptr = next;
	}
    }
    FREE(old_bins);

    return 1;
}

st_table *
st_copy(st_table *old_table)
{
    st_table *new_table;
    st_table_entry *ptr, *newptr, *next, *newt;
    int i, j, num_bins = old_table->num_bins;

    new_table = ALLOC(st_table, 1);
    if (new_table == NIL(st_table)) {
	return NIL(st_table);
    }
    
    *new_table = *old_table;
    new_table->bins = ALLOC(st_table_entry *, num_bins);
    if (new_table->bins == NIL(st_table_entry *)) {
	FREE(new_table);
	return NIL(st_table);
    }
    for(i = 0; i < num_bins ; i++) {
	new_table->bins[i] = NIL(st_table_entry);
	ptr = old_table->bins[i];
	while (ptr != NIL(st_table_entry)) {
	    newt = ALLOC(st_table_entry, 1);
	    if (newt == NIL(st_table_entry)) {
		for (j = 0; j <= i; j++) {
		    newptr = new_table->bins[j];
		    while (newptr != NIL(st_table_entry)) {
			next = newptr->next;
			FREE(newptr);
			newptr = next;
		    }
		}
		FREE(new_table->bins);
		FREE(new_table);
		return NIL(st_table);
	    }
	    *newt = *ptr;
	    newt->next = new_table->bins[i];
	    new_table->bins[i] = newt;
	    ptr = ptr->next;
	}
    }
    return new_table;
}

int
st_delete(st_table *table, char **keyp, char **value)
{
    int hash_val;
    char *key = *keyp;
    register st_table_entry *ptr, **last;

    hash_val = do_hash(key, table);

    FIND_ENTRY(table, hash_val, key, ptr ,last);
    
    if (ptr == NIL(st_table_entry)) {
	return 0;
    }

    *last = ptr->next;
    if (value != NIL(char *)) *value = ptr->record;
    *keyp = ptr->key;
    FREE(ptr);
    table->num_entries--;
    return 1;
}

int
st_delete_int(st_table *table, int *keyp, char **value)
{
    int hash_val;
    char *key = (char *) (util_ptrint) *keyp;
    register st_table_entry *ptr, **last;

    hash_val = do_hash(key, table);

    FIND_ENTRY(table, hash_val, key, ptr ,last);

    if (ptr == NIL(st_table_entry)) {
        return 0;
    }

    *last = ptr->next;
    if (value != NIL(char *)) *value = ptr->record;
    *keyp = (int) (util_ptrint) ptr->key;
    FREE(ptr);
    table->num_entries--;
    return 1;
}

int
st_foreach(st_table *table, ST_PFSR func, char *arg)
{
    st_table_entry *ptr, **last;
    enum st_retval retval;
    int i;

    for(i = 0; i < table->num_bins; i++) {
	last = &table->bins[i]; ptr = *last;
	while (ptr != NIL(st_table_entry)) {
	    retval = (*func)(ptr->key, ptr->record, arg);
	    switch (retval) {
	    case ST_CONTINUE:
		last = &ptr->next; ptr = *last;
		break;
	    case ST_STOP:
		return 0;
	    case ST_DELETE:
		*last = ptr->next;
		table->num_entries--;	/* cstevens@ic */
		FREE(ptr);
		ptr = *last;
	    }
	}
    }
    return 1;
}

int
st_strhash(char *string, int modulus)
{
    register int val = 0;
    register int c;
    
    while ((c = *string++) != '\0') {
	val = val*997 + c;
    }

    return ((val < 0) ? -val : val)%modulus;
}

int
st_numhash(char *x, int size)
{
    return ST_NUMHASH(x, size);
}

int
st_ptrhash(char *x, int size)
{
    return ST_PTRHASH(x, size);
}

int
st_numcmp(const char *x, const char *y)
{
    return ST_NUMCMP(x, y);
}

int
st_ptrcmp(const char *x, const char *y)
{
    return ST_NUMCMP(x, y);
}

st_generator *
st_init_gen(st_table *table)
{
    st_generator *gen;

    gen = ALLOC(st_generator, 1);
    if (gen == NIL(st_generator)) {
	return NIL(st_generator);
    }
    gen->table = table;
    gen->entry = NIL(st_table_entry);
    gen->index = 0;
    return gen;
}


int 
st_gen(st_generator *gen, char **key_p, char **value_p)
{
    register int i;

    if (gen->entry == NIL(st_table_entry)) {
	/* try to find next entry */
	for(i = gen->index; i < gen->table->num_bins; i++) {
	    if (gen->table->bins[i] != NIL(st_table_entry)) {
		gen->index = i+1;
		gen->entry = gen->table->bins[i];
		break;
	    }
	}
	if (gen->entry == NIL(st_table_entry)) {
	    return 0;		/* that's all folks ! */
	}
    }
    *key_p = gen->entry->key;
    if (value_p != 0) {
	*value_p = gen->entry->record;
    }
    gen->entry = gen->entry->next;
    return 1;
}


int 
st_gen_int(st_generator *gen, char **key_p, long *value_p)
{
    register int i;

    if (gen->entry == NIL(st_table_entry)) {
	/* try to find next entry */
	for(i = gen->index; i < gen->table->num_bins; i++) {
	    if (gen->table->bins[i] != NIL(st_table_entry)) {
		gen->index = i+1;
		gen->entry = gen->table->bins[i];
		break;
	    }
	}
	if (gen->entry == NIL(st_table_entry)) {
	    return 0;		/* that's all folks ! */
	}
    }
    *key_p = gen->entry->key;
    if (value_p != NIL(long)) {
   	*value_p = (long) gen->entry->record;
    }
    gen->entry = gen->entry->next;
    return 1;
}


void
st_free_gen(st_generator *gen)
{
    FREE(gen);
}
