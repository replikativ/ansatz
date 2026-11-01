/* Shared-linked pinned runtime conformance oracle; no frontend startup. */
#include <lean/lean.h>
#include <stdio.h>
void lean_initialize_runtime_module(void);
uint8_t lean_string_validate_utf8(b_lean_obj_arg);
static unsigned check(unsigned char const *bytes,size_t length) {
  lean_object *array=lean_alloc_sarray(1,length,length);
  for(size_t i=0;i<length;i++)lean_sarray_cptr(array)[i]=bytes[i];
  unsigned result=lean_string_validate_utf8(array);lean_dec(array);return result;
}
int main(void) {
  lean_initialize_runtime_module();
  unsigned char bytes[5];unsigned one=0,two=0;
  for(unsigned a=0;a<256;a++) {bytes[0]=a;one+=check(bytes,1);
    for(unsigned b=0;b<256;b++){bytes[1]=b;two+=check(bytes,2);}}
  printf("one=%u two=%u\n",one,two);
  unsigned char rows[][6]={{0},{0},{127},{128},{191},{192,128},{193,191},{194,128},{223,191},{194},{194,127},
    {224,160,128},{224,159,191},{237,159,191},{237,160,128},{237,191,191},{238,128,128},{239,191,191},
    {240,144,128,128},{240,143,191,191},{244,143,191,191},{244,144,128,128},{245,128,128,128},
    {248,136,128,128,128},{255},{224},{224,160},{240},{240,144},{240,144,128}};
  unsigned lengths[]={0,1,1,1,1,2,2,2,2,1,2,3,3,3,3,3,3,3,4,4,4,4,4,5,1,1,2,1,2,3};
  unsigned expected[]={1,1,1,0,0,0,0,1,1,0,0,1,0,1,0,0,1,1,1,0,1,0,0,0,0,0,0,0,0,0};
  unsigned errors=0;
  for(unsigned i=0;i<sizeof(lengths)/sizeof(lengths[0]);i++) {
    unsigned actual=check(rows[i],lengths[i]);if(actual!=expected[i]){printf("mismatch=%u\n",i);errors++;}}
  printf("boundaryRows=%zu mismatches=%u\n",sizeof(lengths)/sizeof(lengths[0]),errors);
  return errors || one!=128 || two!=18304;
}
