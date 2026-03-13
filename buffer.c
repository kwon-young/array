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
      if (!PL_get_bool_ex(zero_t, &zero))
      {
        free(p);
        return FALSE;
      }
      if (zero)
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
  if (!PL_get_atom_ex(t, &atom))
  {
    return FALSE;
  }
  PL_free_blob(atom);
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

static foreign_t from_compound(term_t comp, term_t t, term_t type_t, term_t offset_t, term_t it_size)
{
  atom_t type, name;
  size_t arity, size, buffer_size, type_size, comp_offset;
  void *buffer;
  PL_blob_t *blob_type;

  if (PL_get_atom_ex(type_t, &type)
      && atom_size(type, &type_size)
      && PL_get_blob(t, &buffer, &buffer_size, &blob_type)
      && blob_type == &buffer_blob
      && PL_get_size_ex(offset_t, &comp_offset)
      && PL_get_size_ex(it_size, &size)
      && PL_get_compound_name_arity(comp, &name, &arity))
  {
    term_t arg = PL_new_term_ref();
    for (size_t i = 0; i < size; i++)
    {
      if (!PL_get_arg(comp_offset + i + 1, comp, arg) || !set(buffer, buffer_size, type, i, arg)) {
        return FALSE;
      }
    }
    return TRUE;
  }
  return FALSE;
}

static foreign_t to_compound(term_t comp_out, term_t t, term_t type_t, term_t offset_t, term_t it_size, term_t name_t)
{
  atom_t type, name;
  size_t buffer_size, size, type_size, buffer_offset;
  void *buffer;
  PL_blob_t *blob_type;

  if (PL_get_atom_ex(type_t, &type)
      && PL_get_atom_ex(name_t, &name)
      && atom_size(type, &type_size)
      && PL_get_blob(t, &buffer, &buffer_size, &blob_type)
      && blob_type == &buffer_blob
      && PL_get_size_ex(offset_t, &buffer_offset)
      && PL_get_size_ex(it_size, &size))
  {
    buffer += buffer_offset;
    
    term_t args = PL_new_term_refs(size);
    
    for (size_t offset = 0; offset < size; offset++)
    {
      if (!load(buffer, buffer_size, type, offset, args + offset)) {
        return FALSE;
      }
    }
    
    term_t comp = PL_new_term_ref();
    if (!PL_cons_functor_v(comp, PL_new_functor(name, size), args)) {
      return FALSE;
    }
    return PL_unify(comp_out, comp);
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
  PL_register_foreign("cbuffer_alloc", 3, alloc_buffer, 0);
  PL_register_foreign("cbuffer_size", 2, buffer_size, 0);
  PL_register_foreign("cbuffer_free", 1, free_buffer, 0);
  PL_register_foreign("cbuffer_load", 4, load_buffer, 0);
  PL_register_foreign("cbuffer_set", 4, set_buffer, 0);
  PL_register_foreign("cbuffer_type_size", 2, type_size, 0);
  PL_register_foreign("cbuffer_from_compound", 5, from_compound, 0);
  PL_register_foreign("cbuffer_to_compound", 6, to_compound, 0);
  PL_register_foreign("cbuffer_pointer", 3, pointer_buffer, 0);
}
