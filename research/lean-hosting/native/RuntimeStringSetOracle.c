#include <lean/lean.h>
/* Pinned4.33.1 native ownership and exact UTF8 bytes. */
extern int printf(const char *, ...);
void lean_initialize_runtime_module(void);
static void check(unsigned id,const char *s,size_t n,size_t pos,uint32_t cp,int shared,int huge) {
 lean_object *input=lean_mk_string_from_bytes(s,n);
 if(shared)lean_inc(input);
 lean_object *index=huge?lean_nat_add(lean_box(LEAN_MAX_SMALL_NAT),lean_box(1)):lean_box(pos);
 lean_object *out=lean_string_utf8_set(input,index,cp);
 printf("%u %u %zu %zu ",id,out==input,lean_string_size(out)-1,lean_string_len(out));
 for(size_t i=0;i<lean_string_size(out)-1;i++)printf("%02x",(unsigned char)lean_string_cstr(out)[i]);
 printf("\n");lean_dec(out);if(shared)lean_dec(input);lean_dec(index);
}
int main(void) {
 lean_initialize_runtime_module();
 check(0,"PreludeIdentity",15,0,80,0,0);
 check(1,"abc",3,1,66,0,0);check(2,"abc",3,1,66,1,0);
 check(3,"abc",3,1,233,0,0);check(4,"\xc3\xa9\xf0\x9f\x98\x80Z",7,0,65,0,0);
 check(5,"\xc3\xa9\xf0\x9f\x98\x80Z",7,2,955,0,0);
 check(6,"\xc3\xa9\xf0\x9f\x98\x80Z",7,6,128512,0,0);
 check(7,"\xc3\xa9\xf0\x9f\x98\x80Z",7,1,65,0,0);
 check(8,"abc",3,3,65,0,0);check(9,"",0,0,65,0,0);check(10,"abc",3,100,65,0,0);
 check(11,"a\0b",3,1,128512,0,0);check(12,"abc",3,0,0,0,0);check(13,"abc",3,0,65,0,1);
 check(14,"\xc3\xa9" "a",3,2,66,0,0);check(15,"\xc3\xa9",2,0,233,0,0);
 return 0;
}
