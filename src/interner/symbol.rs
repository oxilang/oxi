macro_rules! declare_symbols {
    (@prefill crate) => { "crate" };
    (@prefill super) => { "super" };
    (@prefill self) => { "self" };
    (@prefill Self) => { "Self" };
    (@prefill unit) => { "()" };
    (@prefill $name:ident) => { stringify!($name) };

    (@step $idx:expr; crate, $($rest:tt),*) => {
        pub const crate_: Symbol = $idx;
        declare_symbols!(@step $idx + 1u32; $($rest),*);
    };
    (@step $idx:expr; super, $($rest:tt),*) => {
        pub const super_: Symbol = $idx;
        declare_symbols!(@step $idx + 1u32; $($rest),*);
    };
    (@step $idx:expr; self, $($rest:tt),*) => {
        pub const self_: Symbol = $idx;
        declare_symbols!(@step $idx + 1u32; $($rest),*);
    };
    (@step $idx:expr; Self, $($rest:tt),*) => {
        pub const Self_: Symbol = $idx;
        declare_symbols!(@step $idx + 1u32; $($rest),*);
    };
    (@step $idx:expr; $name:ident, $($rest:tt),*) => {
        pub const $name: Symbol = $idx;
        declare_symbols!(@step $idx + 1u32; $($rest),*);
    };

    (@step $idx:expr; crate) => { pub const crate_: Symbol = $idx; };
    (@step $idx:expr; super) => { pub const super_: Symbol = $idx; };
    (@step $idx:expr; self) => { pub const self_: Symbol = $idx; };
    (@step $idx:expr; Self) => { pub const Self_: Symbol = $idx; };
    (@step $idx:expr; $name:ident) => { pub const $name: Symbol = $idx; };

    ($($name:tt),* $(,)?) => {
        pub(crate) const SYM_PREFILL: &[&str] = &[
            $(declare_symbols!(@prefill $name)),*
        ];

        #[allow(non_upper_case_globals)]
        pub mod sym {
            use crate::interner::Symbol;
            declare_symbols!(@step 0u32; $($name),*);
        }
    };
}

declare_symbols! {
    i8, i16, i32, i64, i128, isize,
    u8, u16, u32, u64, u128, usize,
    f16, f32, f64, f128,
    bool, unit,
    crate, super, self,
    Self,
}
