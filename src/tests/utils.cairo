pub fn assert_equalish<T, impl TPartialOrd: PartialOrd<T>, impl TSub: Sub<T>, impl TCopy: Copy<T>, impl TDrop: Drop<T>>(
    a: T, b: T, error: T, message: felt252
) {
    if a >= b {
        assert(a - b <= error, message);
    } else {
        assert(b - a <= error, message);
    }
}
