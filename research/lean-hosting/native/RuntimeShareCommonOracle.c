/* Pinned Lean4.33.1. Compile using leanc +leanprover/lean4:v4.33.1
 * -o target/runtime-sharecommon-oracle native/RuntimeShareCommonOracle.c
 * -l leanshared -Wl,-rpath,<sysroot>/lib/lean */
#include <lean/lean.h>
extern int printf(const char*, ...);
void lean_initialize_runtime_module(void);
lean_object *lean_sharecommon_quick(lean_object*);
static lean_object *leaf(unsigned scalar) {
 lean_object *r=lean_alloc_ctor(0,0,8); lean_ctor_set_uint64(r,0,scalar); return r;
}
int main(void) {
 lean_initialize_runtime_module();
 lean_object*a=leaf(3),*b=leaf(3),*c=leaf(4);
 lean_object*root=lean_alloc_ctor(1,3,0);
 lean_ctor_set(root,0,a);lean_ctor_set(root,1,b);lean_ctor_set(root,2,c);
 lean_object*r=lean_sharecommon_quick(root);
 printf("ctor %u %u %u %u\n",r!=root,lean_ctor_get(r,0)==lean_ctor_get(r,1),lean_ctor_get(r,0)!=a,lean_ctor_get(r,0)!=lean_ctor_get(r,2));
 lean_object*s1=lean_mk_string("a"),*s2=lean_mk_string("a"),*s3=lean_alloc_string(2,99,1);
 ((lean_string_object*)s3)->m_data[0]='a';((lean_string_object*)s3)->m_data[1]=0;
 /* Native salient body includes capacity, despite ignoring unused bytes. */

 lean_object*t=lean_alloc_ctor(2,3,0);
 lean_ctor_set(t,0,s1);lean_ctor_set(t,1,s2);lean_ctor_set(t,2,s3);
 lean_object*u=lean_sharecommon_quick(t);
 printf("string %u %u\n",lean_ctor_get(u,0)==s1&&lean_ctor_get(u,1)==s1,lean_ctor_get(u,2)==s3);

 lean_object*ar1=lean_alloc_array(1,1),*ar2=lean_alloc_array(1,10);
 lean_array_set_core(ar1,0,lean_box(7));lean_array_set_core(ar2,0,lean_box(7));
 lean_object*ar=lean_alloc_ctor(3,2,0);lean_ctor_set(ar,0,ar1);lean_ctor_set(ar,1,ar2);
 lean_object*av=lean_sharecommon_quick(ar);
 printf("array %u %u\n",lean_ctor_get(av,0)==lean_ctor_get(av,1),lean_ctor_get(av,0)!=ar1);
 lean_dec(av);lean_dec(ar);lean_dec(u);lean_dec(t);lean_dec(r);lean_dec(root);
 return 0;
}
