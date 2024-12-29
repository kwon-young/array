#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <SWI-Prolog.h>

#include "buffer_types.h"

static int release_buffer(atom_t ref)
{
  void *p = PL_blob_data(ref, NULL, NULL);
  if (p)
  {
    free(p);
  }
  return TRUE;
}

static PL_blob_t buffer_blob = {
  PL_BLOB_MAGIC,
  PL_BLOB_UNIQUE | PL_BLOB_NOCOPY,
  "buffer",
  release_buffer,
  NULL,
  NULL,
  NULL,
  NULL,
  NULL
};

static foreign_t alloc_buffer(term_t t, term_t count, term_t zero_t)
{
  if (!PL_is_variable(t))
  {
    PL_uninstantiation_error(t);
    return FALSE;
  }
  size_t size;

  if (PL_get_size_ex(count, &size))
  {
    void *p = malloc(size);

    if (p)
    {
      int zero;
      if (PL_get_bool_ex(zero_t, &zero) && zero)
      {
        memset(p, 0, size);
      }
      if (PL_unify_blob(t, p, size, &buffer_blob))
      {
        return TRUE;
      } else {
        free(p);
      }
    } else {
      PL_resource_error("memory");
    }
  }
  return FALSE;
}

static foreign_t buffer_size(term_t t, term_t count)
{
  PL_blob_t *blob_type;
  if (!PL_is_blob(t, &blob_type) || blob_type != &buffer_blob)
  {
    PL_type_error("buffer", t);
    return FALSE;
  }
  size_t size;
  if (PL_get_blob(t, NULL, &size, NULL)) {
    if (PL_unify_uint64(count, size)) {
      return TRUE;
    }
  }
  return FALSE;
}

static foreign_t free_buffer(term_t t)
{
  PL_blob_t *blob_type;
  if (!PL_is_blob(t, &blob_type) || blob_type != &buffer_blob)
  {
    PL_type_error("buffer", t);
    return FALSE;
  }
  atom_t atom;
  if (PL_get_atom_ex(t, &atom))
  {
    PL_free_blob(atom);
  }
  return TRUE;
}

static foreign_t set_buffer(term_t t, term_t type_t, term_t i, term_t v)
{
  atom_t type;
  size_t size;
  void *buffer;
  PL_blob_t *blob_type;
  size_t offset;

  if (PL_get_atom_ex(type_t, &type)
      && PL_get_size_ex(i, &offset)
      && PL_get_blob(t, &buffer, &size, &blob_type)
      && blob_type == &buffer_blob)
  {
    return set(buffer, size, type, offset, v);
  }
  PL_type_error("buffer", t);
  return FALSE;
}

static foreign_t load_buffer(term_t t, term_t type_t, term_t i, term_t v)
{
  atom_t type;
  size_t offset, size;
  void *buffer;
  PL_blob_t *blob_type;

  if (PL_get_atom_ex(type_t, &type)
      && PL_get_size_ex(i, &offset)
      && PL_get_blob(t, &buffer, &size, &blob_type)
      && blob_type == &buffer_blob)
  {
    return load(buffer, size, type, offset, v);
  }
  PL_type_error("buffer", t);
  return FALSE;
}

static foreign_t type_size(term_t type_t, term_t size)
{
  atom_t type;
  size_t size_;
  if (PL_get_atom_ex(type_t, &type))
  {
    return atom_size(type, &size_) && PL_unify_uint64(size, size_);
  }
  return FALSE;
}

static foreign_t from_list(term_t l, term_t t, term_t type_t)
{
  term_t head = PL_new_term_ref();
  term_t tail = PL_copy_term_ref(l);
  atom_t type;
  size_t offset = 0, size;
  void *buffer;
  PL_blob_t *blob_type;

  if (PL_get_atom_ex(type_t, &type)
      && PL_get_blob(t, &buffer, &size, &blob_type)
      && blob_type == &buffer_blob)
  {
    while(PL_get_list_ex(tail, head, tail))
    {
      if (!set(buffer, size, type, offset, head)) {
        return FALSE;
      }
      offset++;
    }
    return PL_get_nil_ex(tail);
  }
  return FALSE;
}

static foreign_t to_list(term_t l, term_t t, term_t type_t, term_t offset_t, term_t it_size)
{
  term_t head = PL_new_term_ref();
  term_t tail = PL_copy_term_ref(l);
  atom_t type;
  size_t buffer_size, size, type_size, buffer_offset;
  void *buffer;
  PL_blob_t *blob_type;

  if (PL_get_atom_ex(type_t, &type)
      && atom_size(type, &type_size)
      && PL_get_blob(t, &buffer, &buffer_size, &blob_type)
      && blob_type == &buffer_blob
      && PL_get_size_ex(offset_t, &buffer_offset)
      && PL_get_size_ex(it_size, &size))
 {
    buffer += buffer_offset;
    for (size_t offset = 0; offset < size; offset++)
    {
      if (!PL_unify_list(tail, head, tail)
          || !load(buffer, buffer_size, type, offset, head)) {
        return FALSE;
      }
    }
    return PL_unify_nil(tail);
  }
  return FALSE;
}

static foreign_t pointer_buffer(term_t p, term_t t, term_t offset_t)
{
  size_t offset, size;
  void *buffer;
  PL_blob_t *blob_type;
  if (PL_get_uint64_ex(offset_t, &offset)
      && PL_get_blob(t, &buffer, &size, &blob_type)
      && blob_type == &buffer_blob
      && offset <= size
      && PL_unify_pointer(p, (void*)((char*)(buffer)+offset)))
  {
    return TRUE;
  }
  return FALSE;
}


install_t install(void)
{
  install_types();
  PL_register_foreign("alloc_buffer", 3, alloc_buffer, 0);
  PL_register_foreign("buffer_size", 2, buffer_size, 0);
  PL_register_foreign("free_buffer", 1, free_buffer, 0);
  PL_register_foreign("load_buffer", 4, load_buffer, 0);
  PL_register_foreign("set_buffer", 4, set_buffer, 0);
  PL_register_foreign("type_size", 2, type_size, 0);
  PL_register_foreign("from_list", 3, from_list, 0);
  PL_register_foreign("to_list", 5, to_list, 0);
  PL_register_foreign("pointer_buffer", 3, pointer_buffer, 0);
}
