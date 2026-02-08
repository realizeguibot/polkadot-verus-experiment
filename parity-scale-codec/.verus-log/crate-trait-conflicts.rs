#![feature(negative_impls)]
#![feature(with_negative_coherence)]
#![feature(box_patterns)]
#![feature(ptr_metadata)]
#![feature(never_type)]
#![feature(allocator_api)]
#![feature(unboxed_closures)]
#![feature(fn_traits)]
#![feature(tuple_trait)]
#![feature(f16)]
#![feature(f128)]
#![allow(non_camel_case_types)]
#![allow(unused_imports)]
#![allow(unused_variables)]
#![allow(unused_assignments)]
#![allow(unreachable_patterns)]
#![allow(unused_parens)]
#![allow(unused_braces)]
#![allow(dead_code)]
#![allow(unreachable_code)]
#![allow(unconditional_recursion)]
#![allow(unused_mut)]
#![allow(unused_labels)]
use std::marker::PhantomData;
use std::marker::Tuple;
use std::rc::Rc;
use std::sync::Arc;
use std::alloc::Allocator;
use std::alloc::Global;
use std::mem::ManuallyDrop;
use std::ptr::Pointee;
use std::ptr::Thin;
fn op<A, B>(a: A) -> B { panic!() }
fn static_ref<T>(t: T) -> &'static T { panic!() }
fn tracked_new<T>(t: T) -> Tracked<T> { panic!() }
fn tracked_exec_borrow<'a, T>(t: &'a T) -> &'a Tracked<T> { panic!() }
fn clone<T>(t: &T) -> T { panic!() }
fn rc_new<T>(t: T) -> std::rc::Rc<T> { panic!() }
fn arc_new<T>(t: T) -> std::sync::Arc<T> { panic!() }
fn box_new<T>(t: T) -> Box<T> { panic!() }
struct Tracked<A> { a: PhantomData<A> }
impl<A> Tracked<A> {
    pub fn get(self) -> A { panic!() }
    pub fn borrow(&self) -> &A { panic!() }
    pub fn borrow_mut(&mut self) -> &mut A { panic!() }
}
struct Ghost<A> { a: PhantomData<A> }
impl<A> Clone for Ghost<A> { fn clone(&self) -> Self { panic!() } }
impl<A> Copy for Ghost<A> { }
impl<A: Copy> Clone for Tracked<A> { fn clone(&self) -> Self { panic!() } }
impl<A: Copy> Copy for Tracked<A> { }
#[derive(Clone, Copy)] struct int;
#[derive(Clone, Copy)] struct nat;
#[derive(Clone, Copy)] struct real;
struct FnSpec<Args, Output> { x: PhantomData<(Args, Output)> }
struct InvariantBlockGuard;
fn open_atomic_invariant_begin<'a, X, V>(_inv: &'a X) -> (InvariantBlockGuard, V) { panic!(); }
fn open_local_invariant_begin<'a, X, V>(_inv: &'a X) -> (InvariantBlockGuard, V) { panic!(); }
fn open_invariant_end<V>(_guard: InvariantBlockGuard, _v: V) { panic!() }
fn index<'a, V, Idx, Output>(v: &'a V, index: Idx) -> &'a Output { panic!() }
trait IndexSet{
fn index_set<Idx, V>(&mut self, index: Idx, val: V) { panic!() }
}
impl<A:?Sized> IndexSet for A {}
struct C<const N: usize, A: ?Sized>(Box<A>);
struct Arr<A: ?Sized, const N: usize>(Box<A>);
struct Dyn<const N: usize, A>(Box<A>, [bool]);
fn use_type_invariant<A>(a: A) -> A { a }

struct FnProof<'a, P, M, N, A, O>(PhantomData<P>, PhantomData<M>, PhantomData<N>, PhantomData<&'a fn(A) -> O>);
struct FOpts<const B: u8, C, const D: u8, const E: u8, const G: u8>(PhantomData<C>);
trait ProofFnOnce {}
trait ProofFnMut: ProofFnOnce {}
trait ProofFn: ProofFnMut {}
struct ProofFnConfirm;
trait ConfirmCopy<const D: u8, F> {}
trait ConfirmUsage<A, O, const B: u8, F> {}
impl<const B: u8, C, const E: u8, const G: u8> Clone for FOpts<B, C, 4, E, G> { fn clone(&self) -> Self { panic!() } }
impl<const B: u8, C, const E: u8, const G: u8> Copy for FOpts<B, C, 4, E, G> {}
impl<const B: u8, C, const D: u8, const E: u8, const G: u8> ProofFnOnce for FOpts<B, C, D, E, G> {}
impl<C, const D: u8, const E: u8, const G: u8> ProofFnMut for FOpts<2, C, D, E, G> {}
impl<C, const D: u8, const E: u8, const G: u8> ProofFnMut for FOpts<3, C, D, E, G> {}
impl<C, const D: u8, const E: u8, const G: u8> ProofFn for FOpts<3, C, D, E, G> {}
impl<'a, P: Copy, M, N, A, O> Clone for FnProof<'a, P, M, N, A, O> { fn clone(&self) -> Self { panic!() } }
impl<'a, P: Copy, M, N, A, O> Copy for FnProof<'a, P, M, N, A, O> {}
impl<'a, P: ProofFnOnce, M, N, A: Tuple, O> FnOnce<A> for FnProof<'a, P, M, N, A, O> {
    type Output = O;
    extern "rust-call" fn call_once(self, _: A) -> <Self as FnOnce<A>>::Output { panic!() }
}
impl<'a, P: ProofFnMut, M, N, A: Tuple, O> FnMut<A> for FnProof<'a, P, M, N, A, O> {
    extern "rust-call" fn call_mut(&mut self, _: A) -> <Self as FnOnce<A>>::Output { panic!() }
}
impl<'a, P: ProofFn, M, N, A: Tuple, O> Fn<A> for FnProof<'a, P, M, N, A, O> {
    extern "rust-call" fn call(&self, _: A) -> <Self as FnOnce<A>>::Output { panic!() }
}
impl<F: Copy> ConfirmCopy<4, F> for ProofFnConfirm {}
impl<F> ConfirmCopy<0, F> for ProofFnConfirm {}
impl<A: Tuple, O, F: FnOnce<A, Output = O>> ConfirmUsage<A, O, 1, F> for ProofFnConfirm {}
impl<A: Tuple, O, F: FnMut<A, Output = O>> ConfirmUsage<A, O, 2, F> for ProofFnConfirm {}
impl<A: Tuple, O, F: Fn<A, Output = O>> ConfirmUsage<A, O, 3, F> for ProofFnConfirm {}
pub fn closure_to_fn_proof<'a, const B: u8, const D: u8, const E: u8, const G: u8, M, N, A, O, F: 'a>(_f: F) -> FnProof<'a, FOpts<B, (), D, E, G>, M, N, A, O>
where ProofFnConfirm: ConfirmUsage<A, O, B, F>, ProofFnConfirm: ConfirmCopy<D, F>, M: Tuple, A: Tuple,
{ panic!() }

fn main() {}



trait T15_ArrayAdditionalSpecFns<A3_T, > where Self: T14_View, Self: T14_View<A1_V = D11_Seq<A3_T, >>,  {
}

trait T16_SliceAdditionalSpecFns<A3_T, > where Self: T14_View, Self: T14_View<A1_V = D11_Seq<A3_T, >>,  {
}

trait T14_View {
    type A1_V : ;
}

trait T17_DeepView {
    type A1_V : ;
}

trait T18_Clone where Self: Sized,  {
}

trait T19_From<A3_T, > where Self: Sized,  {
}

trait T20_FromSpec<A3_T, > where Self: Sized, Self: T19_From<A3_T, >,  {
}

trait T7_Allocator {
}

trait T21_Debug {
}

trait T22_OptionAdditionalFns<A3_T, > where Self: Sized,  {
}

trait T23_ResultAdditionalSpecFns<A3_T, A4_E, > where  {
}

trait T24_VecAdditionalSpecFns<A3_T, > where Self: T14_View, Self: T14_View<A1_V = D11_Seq<A3_T, >>,  {
}

struct D2_Option<A1_V, >(
    Box<A1_V, >,
) where ;

struct D5_Result<A3_T, A4_E, >(
    Box<A3_T, >,
    Box<A4_E, >,
) where ;

struct D8_Vec<A3_T, A6_A, >(
    Box<A3_T, >,
    Box<A6_A, >,
) where A6_A: T7_Allocator, ;

struct D9_Provenance(
);

struct D10_PtrData<A3_T, >(
    Box<A3_T, >,
    <A3_T as std::ptr::Pointee>::Metadata,
) where A3_T : ?Sized, ;

struct D11_Seq<A6_A, >(
    Box<A6_A, >,
) where ;

struct D12_Set<A6_A, >(
    Box<A6_A, >,
    C<0, (Box<(A6_A, ), >, Box<bool, >, ), >,
) where ;

struct D13_Error(
);

impl<A3_T, const A25_N: usize, > T14_View for Arr<A3_T, A25_N, > where  {
    type A1_V = D11_Seq<A3_T, >;
}

impl<A3_T, const A25_N: usize, > T17_DeepView for Arr<A3_T, A25_N, > where A3_T: T17_DeepView,  {
    type A1_V = D11_Seq<<A3_T as T17_DeepView>::A1_V, >;
}

impl<A3_T, const A25_N: usize, > T15_ArrayAdditionalSpecFns<A3_T, > for Arr<A3_T, A25_N, > where  {
}

impl<A3_T, > T14_View for C<1, (Box<A3_T, >, ), > where A3_T : ?Sized,  {
    type A1_V = D10_PtrData<A3_T, >;
}

impl<A3_T, > T14_View for C<10, (Box<C<1, (Box<A3_T, >, ), >, >, ), > where A3_T : ?Sized,  {
    type A1_V = D10_PtrData<A3_T, >;
}

impl<A3_T, > T14_View for [A3_T] where  {
    type A1_V = D11_Seq<A3_T, >;
}

impl<A3_T, > T17_DeepView for [A3_T] where A3_T: T17_DeepView,  {
    type A1_V = D11_Seq<<A3_T as T17_DeepView>::A1_V, >;
}

impl<A3_T, > T16_SliceAdditionalSpecFns<A3_T, > for [A3_T] where  {
}

impl T14_View for str {
    type A1_V = D11_Seq<char, >;
}

impl T17_DeepView for str {
    type A1_V = D11_Seq<char, >;
}

impl<A6_A, > T14_View for C<2, (Box<A6_A, >, ), > where A6_A: T14_View, A6_A : ?Sized,  {
    type A1_V = <A6_A as T14_View>::A1_V;
}

impl<A6_A, > T17_DeepView for C<2, (Box<A6_A, >, ), > where A6_A: T17_DeepView, A6_A : ?Sized,  {
    type A1_V = <A6_A as T17_DeepView>::A1_V;
}

impl<A6_A, > T14_View for C<4, (Box<A6_A, >, Box<C<11, (), >, >, ), > where A6_A: T14_View, A6_A : ?Sized,  {
    type A1_V = <A6_A as T14_View>::A1_V;
}

impl<A6_A, > T17_DeepView for C<4, (Box<A6_A, >, Box<C<11, (), >, >, ), > where A6_A: T17_DeepView, A6_A : ?Sized,  {
    type A1_V = <A6_A as T17_DeepView>::A1_V;
}

impl<A6_A, > T14_View for C<5, (Box<A6_A, >, Box<C<11, (), >, >, ), > where A6_A: T14_View,  {
    type A1_V = <A6_A as T14_View>::A1_V;
}

impl<A6_A, > T17_DeepView for C<5, (Box<A6_A, >, Box<C<11, (), >, >, ), > where A6_A: T17_DeepView,  {
    type A1_V = <A6_A as T17_DeepView>::A1_V;
}

impl<A6_A, > T14_View for C<6, (Box<A6_A, >, Box<C<11, (), >, >, ), > where A6_A: T14_View,  {
    type A1_V = <A6_A as T14_View>::A1_V;
}

impl<A6_A, > T17_DeepView for C<6, (Box<A6_A, >, Box<C<11, (), >, >, ), > where A6_A: T17_DeepView,  {
    type A1_V = <A6_A as T17_DeepView>::A1_V;
}

impl<A3_T, A6_A, > T14_View for D8_Vec<A3_T, A6_A, > where A6_A: T7_Allocator,  {
    type A1_V = D11_Seq<A3_T, >;
}

impl<A3_T, A6_A, > T17_DeepView for D8_Vec<A3_T, A6_A, > where A3_T: T17_DeepView, A6_A: T7_Allocator,  {
    type A1_V = D11_Seq<<A3_T as T17_DeepView>::A1_V, >;
}

impl<A3_T, > T14_View for D2_Option<A3_T, > where  {
    type A1_V = D2_Option<A3_T, >;
}

impl<A3_T, > T17_DeepView for D2_Option<A3_T, > where A3_T: T17_DeepView,  {
    type A1_V = D2_Option<<A3_T as T17_DeepView>::A1_V, >;
}

impl T14_View for () {
    type A1_V = ();
}

impl T17_DeepView for () {
    type A1_V = ();
}

impl T14_View for bool {
    type A1_V = bool;
}

impl T17_DeepView for bool {
    type A1_V = bool;
}

impl T14_View for u8 {
    type A1_V = u8;
}

impl T17_DeepView for u8 {
    type A1_V = u8;
}

impl T14_View for u16 {
    type A1_V = u16;
}

impl T17_DeepView for u16 {
    type A1_V = u16;
}

impl T14_View for u32 {
    type A1_V = u32;
}

impl T17_DeepView for u32 {
    type A1_V = u32;
}

impl T14_View for u64 {
    type A1_V = u64;
}

impl T17_DeepView for u64 {
    type A1_V = u64;
}

impl T14_View for u128 {
    type A1_V = u128;
}

impl T17_DeepView for u128 {
    type A1_V = u128;
}

impl T14_View for usize {
    type A1_V = usize;
}

impl T17_DeepView for usize {
    type A1_V = usize;
}

impl T14_View for i8 {
    type A1_V = i8;
}

impl T17_DeepView for i8 {
    type A1_V = i8;
}

impl T14_View for i16 {
    type A1_V = i16;
}

impl T17_DeepView for i16 {
    type A1_V = i16;
}

impl T14_View for i32 {
    type A1_V = i32;
}

impl T17_DeepView for i32 {
    type A1_V = i32;
}

impl T14_View for i64 {
    type A1_V = i64;
}

impl T17_DeepView for i64 {
    type A1_V = i64;
}

impl T14_View for i128 {
    type A1_V = i128;
}

impl T17_DeepView for i128 {
    type A1_V = i128;
}

impl T14_View for isize {
    type A1_V = isize;
}

impl T17_DeepView for isize {
    type A1_V = isize;
}

impl T14_View for char {
    type A1_V = char;
}

impl T17_DeepView for char {
    type A1_V = char;
}

impl<A26_A0, > T14_View for (Box<A26_A0, >, ) where A26_A0: T14_View,  {
    type A1_V = (Box<<A26_A0 as T14_View>::A1_V, >, );
}

impl<A26_A0, > T17_DeepView for (Box<A26_A0, >, ) where A26_A0: T17_DeepView,  {
    type A1_V = (Box<<A26_A0 as T17_DeepView>::A1_V, >, );
}

impl<A26_A0, A27_A1, > T14_View for (Box<A26_A0, >, Box<A27_A1, >, ) where A26_A0: T14_View, A27_A1: T14_View,  {
    type A1_V = (Box<<A26_A0 as T14_View>::A1_V, >, Box<<A27_A1 as T14_View>::A1_V, >, );
}

impl<A26_A0, A27_A1, > T17_DeepView for (Box<A26_A0, >, Box<A27_A1, >, ) where A26_A0: T17_DeepView, A27_A1: T17_DeepView,  {
    type A1_V = (Box<<A26_A0 as T17_DeepView>::A1_V, >, Box<<A27_A1 as T17_DeepView>::A1_V, >, );
}

impl T20_FromSpec<u8, > for u16 {
}

impl T20_FromSpec<u8, > for u32 {
}

impl T20_FromSpec<u8, > for u64 {
}

impl T20_FromSpec<u8, > for usize {
}

impl T20_FromSpec<u8, > for u128 {
}

impl T20_FromSpec<u16, > for u32 {
}

impl T20_FromSpec<u16, > for u64 {
}

impl T20_FromSpec<u16, > for usize {
}

impl T20_FromSpec<u16, > for u128 {
}

impl T20_FromSpec<u32, > for u64 {
}

impl T20_FromSpec<u32, > for u128 {
}

impl T20_FromSpec<u64, > for u128 {
}

impl<A3_T, > T22_OptionAdditionalFns<A3_T, > for D2_Option<A3_T, > where  {
}

impl<A3_T, A4_E, > T23_ResultAdditionalSpecFns<A3_T, A4_E, > for D5_Result<A3_T, A4_E, > where  {
}

impl<A3_T, A6_A, > T24_VecAdditionalSpecFns<A3_T, > for D8_Vec<A3_T, A6_A, > where A6_A: T7_Allocator,  {
}

impl T18_Clone for usize {
}

impl T18_Clone for u8 {
}

impl T18_Clone for u16 {
}

impl T18_Clone for u32 {
}

impl T18_Clone for u64 {
}

impl T18_Clone for u128 {
}

impl T18_Clone for isize {
}

impl T18_Clone for i8 {
}

impl T18_Clone for i16 {
}

impl T18_Clone for i32 {
}

impl T18_Clone for i64 {
}

impl T18_Clone for i128 {
}

impl T18_Clone for bool {
}

impl T18_Clone for char {
}

impl<A3_T, > T18_Clone for C<10, (Box<C<1, (Box<A3_T, >, ), >, >, ), > where A3_T : ?Sized,  {
}

impl<A3_T, > T18_Clone for C<1, (Box<A3_T, >, ), > where A3_T : ?Sized,  {
}

impl<A3_T, > T18_Clone for C<2, (Box<A3_T, >, ), > where A3_T : ?Sized,  {
}

impl<A3_T, const A25_N: usize, > T18_Clone for Arr<A3_T, A25_N, > where A3_T: T18_Clone,  {
}

impl<A3_T, A4_E, > T18_Clone for D5_Result<A3_T, A4_E, > where A3_T: T18_Clone, A4_E: T18_Clone,  {
}

impl T18_Clone for C<11, (), > {
}

impl<A3_T, A6_A, > T18_Clone for D8_Vec<A3_T, A6_A, > where A3_T: T18_Clone, A6_A: T7_Allocator, A6_A: T18_Clone,  {
}

impl<A3_T, > T19_From<A3_T, > for A3_T where  {
}

impl T19_From<bool, > for usize {
}

impl T19_From<u8, > for usize {
}

impl T19_From<u16, > for usize {
}

impl T19_From<bool, > for u8 {
}

impl T19_From<bool, > for u16 {
}

impl T19_From<u8, > for u16 {
}

impl T19_From<bool, > for u32 {
}

impl T19_From<u8, > for u32 {
}

impl T19_From<u16, > for u32 {
}

impl T19_From<char, > for u32 {
}

impl T19_From<bool, > for u64 {
}

impl T19_From<u8, > for u64 {
}

impl T19_From<u16, > for u64 {
}

impl T19_From<u32, > for u64 {
}

impl T19_From<char, > for u64 {
}

impl T19_From<bool, > for u128 {
}

impl T19_From<u8, > for u128 {
}

impl T19_From<u16, > for u128 {
}

impl T19_From<u32, > for u128 {
}

impl T19_From<u64, > for u128 {
}

impl T19_From<char, > for u128 {
}

impl T19_From<bool, > for i8 {
}

impl T19_From<bool, > for i16 {
}

impl T19_From<i8, > for i16 {
}

impl T19_From<u8, > for i16 {
}

impl T19_From<bool, > for i32 {
}

impl T19_From<i8, > for i32 {
}

impl T19_From<i16, > for i32 {
}

impl T19_From<u8, > for i32 {
}

impl T19_From<u16, > for i32 {
}

impl T19_From<bool, > for i64 {
}

impl T19_From<i8, > for i64 {
}

impl T19_From<i16, > for i64 {
}

impl T19_From<i32, > for i64 {
}

impl T19_From<u8, > for i64 {
}

impl T19_From<u16, > for i64 {
}

impl T19_From<u32, > for i64 {
}

impl T19_From<bool, > for i128 {
}

impl T19_From<i8, > for i128 {
}

impl T19_From<i16, > for i128 {
}

impl T19_From<i32, > for i128 {
}

impl T19_From<i64, > for i128 {
}

impl T19_From<u8, > for i128 {
}

impl T19_From<u16, > for i128 {
}

impl T19_From<u32, > for i128 {
}

impl T19_From<u64, > for i128 {
}

impl T19_From<bool, > for isize {
}

impl T19_From<i8, > for isize {
}

impl T19_From<u8, > for isize {
}

impl T19_From<i16, > for isize {
}

impl T19_From<u8, > for char {
}

impl<A3_T, > T19_From<A3_T, > for D2_Option<A3_T, > where  {
}

impl<A3_T, > T19_From<C<2, (Box<D2_Option<A3_T, >, >, ), >, > for D2_Option<C<2, (Box<A3_T, >, ), >, > where  {
}

impl<A3_T, > T19_From<Arr<A3_T, 1, >, > for (Box<A3_T, >, ) where  {
}

impl<A3_T, > T19_From<(Box<A3_T, >, ), > for Arr<A3_T, 1, > where  {
}

impl<A3_T, > T19_From<(Box<A3_T, >, Box<A3_T, >, ), > for Arr<A3_T, 2, > where  {
}

impl<A3_T, > T19_From<Arr<A3_T, 2, >, > for (Box<A3_T, >, Box<A3_T, >, ) where  {
}

impl<A3_T, > T19_From<C<2, (Box<[A3_T], >, ), >, > for D8_Vec<A3_T, C<11, (), >, > where A3_T: T18_Clone,  {
}

impl<A3_T, const A25_N: usize, > T19_From<C<2, (Box<Arr<A3_T, A25_N, >, >, ), >, > for D8_Vec<A3_T, C<11, (), >, > where A3_T: T18_Clone,  {
}

impl<A3_T, const A25_N: usize, > T19_From<Arr<A3_T, A25_N, >, > for D8_Vec<A3_T, C<11, (), >, > where  {
}

impl T19_From<C<2, (Box<str, >, ), >, > for D8_Vec<u8, C<11, (), >, > {
}

impl<A3_T, const A25_N: usize, > T21_Debug for Arr<A3_T, A25_N, > where A3_T: T21_Debug,  {
}

impl<A3_T, > T21_Debug for D2_Option<A3_T, > where A3_T: T21_Debug,  {
}

impl<A3_T, A4_E, > T21_Debug for D5_Result<A3_T, A4_E, > where A3_T: T21_Debug, A4_E: T21_Debug,  {
}

impl T21_Debug for i8 {
}

impl T21_Debug for i16 {
}

impl T21_Debug for i32 {
}

impl T21_Debug for i64 {
}

impl T21_Debug for i128 {
}

impl T21_Debug for isize {
}

impl T21_Debug for u8 {
}

impl T21_Debug for u16 {
}

impl T21_Debug for u32 {
}

impl T21_Debug for u64 {
}

impl T21_Debug for u128 {
}

impl T21_Debug for usize {
}

impl<A3_T, > T21_Debug for C<2, (Box<A3_T, >, ), > where A3_T: T21_Debug, A3_T : ?Sized,  {
}

impl T21_Debug for bool {
}

impl T21_Debug for str {
}

impl T21_Debug for char {
}

impl<A3_T, > T21_Debug for C<10, (Box<C<1, (Box<A3_T, >, ), >, >, ), > where A3_T : ?Sized,  {
}

impl<A3_T, > T21_Debug for C<1, (Box<A3_T, >, ), > where A3_T : ?Sized,  {
}

impl<A28_U, A3_T, > T21_Debug for (Box<A28_U, >, Box<A3_T, >, ) where A28_U: T21_Debug, A3_T: T21_Debug,  {
}

impl<A3_T, > T21_Debug for (Box<A3_T, >, ) where A3_T: T21_Debug,  {
}

impl<A3_T, > T21_Debug for [A3_T] where A3_T: T21_Debug,  {
}

impl T21_Debug for () {
}

impl T21_Debug for C<11, (), > {
}

impl<A3_T, A6_A, > T21_Debug for D8_Vec<A3_T, A6_A, > where A3_T: T21_Debug, A6_A: T7_Allocator,  {
}

impl<A6_A, > T7_Allocator for C<2, (Box<A6_A, >, ), > where A6_A: T7_Allocator, A6_A : ?Sized,  {
}

impl T7_Allocator for C<11, (), > {
}

impl<A6_A, > T18_Clone for C<8, (Box<A6_A, >, ), > where  {
}

impl<A6_A, > T18_Clone for C<7, (Box<A6_A, >, ), > where  {
}

impl<A3_T, > T18_Clone for D2_Option<A3_T, > where A3_T: T18_Clone,  {
}

impl<A3_T, A6_A, > T18_Clone for C<4, (Box<A3_T, >, Box<A6_A, >, ), > where A3_T: T18_Clone, A6_A: T7_Allocator, A6_A: T18_Clone,  {
}

impl T18_Clone for D13_Error {
}

impl T19_From<C<2, (Box<str, >, ), >, > for D13_Error {
}

impl T21_Debug for D13_Error {
}
