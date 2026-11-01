#include <lean/lean.h>
/* Reproduce with:
 * leanc +leanprover/lean4:v4.33.1 -o target/runtime-string-oracle native/RuntimeStringOracle.c
 * target/runtime-string-oracle
 * The release leanc sysroot omits stdio.h; use printf's standard declaration.
 * All offsets printed below are UTF-8 byte offsets. Hashes are unsigned UInt64.
 */
extern int printf(const char *, ...);
void lean_initialize_runtime_module(void);
lean_object *lean_string_posof(lean_object *, uint32_t);
int main(void) {
 lean_initialize_runtime_module();
 const char* inputs[]={"", "a", "abcdefg", "abcdefgh", "abcdefghi", "\xc3\xa9\xf0\x9f\x98\x80Z", "\xee\x80\x80", "\xf0\x90\x80\x80"};
 for(unsigned i=0;i<8;i++){lean_object*s=lean_mk_string(inputs[i]);printf("hash %u %llu\n",i,(unsigned long long)lean_string_hash(s));}
 lean_object*s=lean_mk_string(inputs[5]);
 for(size_t i=0;i<10;i++){lean_object*p=lean_box(i);printf("pos %zu %u %zu %u\n",i,lean_string_utf8_get(s,p),lean_unbox(lean_string_utf8_next(s,p)),lean_string_utf8_at_end(s,p));}
 lean_object*a=lean_mk_string(inputs[6]);lean_object*b=lean_mk_string(inputs[7]);
 printf("cmp %u %u %u\n",lean_string_compare(a,b),lean_string_compare(a,a),lean_string_compare(b,a));
 printf("mix %llu %llu %llu\n",(unsigned long long)lean_uint64_mix_hash(0,0),(unsigned long long)lean_uint64_mix_hash(1,2),(unsigned long long)lean_uint64_mix_hash(UINT64_MAX,UINT64_MAX));
 lean_object*huge=lean_nat_add(lean_box(LEAN_MAX_SMALL_NAT),lean_box(1));
 lean_object*x=lean_string_utf8_extract(s,lean_box(0),huge);
 printf("hugeExtract %zu\n",lean_string_size(x)-1);
 const char* search[]={"", "abc", "a\nb\n", "\xc3\xa9\xf0\x9f\x98\x80\n\xce\xbb",
 "\xc3\xa9\xf0\x9f\x98\x80\n\xce\xbb", "\xc3\xa9\xf0\x9f\x98\x80\n\xce\xbb",
 "\xc3\xa9\xf0\x9f\x98\x80\n\xce\xbb", "\xc3\xa9\xf0\x9f\x98\x80\n\xce\xbb",
 "a\0b", "\xf0\x9f\x98\x80\xc3\xa9\xf0\x9f\x98\x80", "\xf0\x90\x80\x80\xee\x80\x80", "x\r\ny"};
 const uint32_t cps[]={10,10,10,10,233,128512,955,90,0,128512,57344,10};
 for(unsigned i=0;i<12;i++) {
   lean_object*str=i==8 ? lean_mk_string_from_bytes(search[i],3) : lean_mk_string(search[i]);
   lean_object*pos=lean_string_posof(str,cps[i]);
   printf("posof %u %zu\n",i,lean_unbox(pos)); lean_dec(pos);
 }
 return 0;
}
