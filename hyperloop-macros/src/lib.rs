#![feature(proc_macro_diagnostic)]
#![feature(box_into_inner)]

use darling::FromMeta;
use proc_macro::TokenStream;
use quote::{format_ident, quote};
use syn::{
    parse::Parse,
    punctuated::{Pair, Punctuated},
    spanned::Spanned,
    token::Comma,
    Expr, FnArg, Ident, Pat, Token,
};

#[derive(Debug, FromMeta)]
struct TaskArgs {
    priority: u8,
}

/// Attribute macro for creating statically allocated async task
///
/// # Example
/// ```
/// #[task(priority = 1)]
/// async fn task() {
///     loop {
///         // Do stuff in here
///     }
/// }
///
/// let task_handle = task().unwrap();
/// ```
///
#[proc_macro_attribute]
pub fn task(args: TokenStream, item: TokenStream) -> TokenStream {
    let macro_args = syn::parse_macro_input!(args as syn::AttributeArgs);
    let mut task_fn = syn::parse_macro_input!(item as syn::ItemFn);

    let macro_args = match TaskArgs::from_list(&macro_args) {
        Ok(v) => v,
        Err(e) => {
            return TokenStream::from(e.write_errors());
        }
    };

    let priority = macro_args.priority;

    if task_fn.sig.asyncness.is_none() {
        task_fn
            .sig
            .span()
            .unwrap()
            .error("task functions must be async")
            .emit();
        return TokenStream::new();
    }

    let name = task_fn.sig.ident.clone();
    let args = task_fn.sig.inputs.clone();
    let arg_values: Punctuated<Ident, Comma> = args
        .pairs()
        .filter_map(|pair| {
            let (arg, punct) = pair.into_tuple();

            if let FnArg::Typed(pat_type) = arg {
                if let Pat::Ident(pat_ident) = *pat_type.pat.clone() {
                    Some(Pair::new(pat_ident.ident, punct.copied()))
                } else {
                    None
                }
            } else {
                None
            }
        })
        .collect();

    let visibility = &task_fn.vis;
    task_fn.sig.ident = format_ident!("task");
    let future_type = quote!(impl ::core::future::Future<Output = ()> + 'static);
    let attrs = &task_fn.attrs;

    let result = quote! {
        #(#attrs)*
        #visibility fn #name(#args) -> Option<::hyperloop::task::TaskHandle> {
            mod inner {
                use super::*;

                pub type F = #future_type;

                pub fn wrapper(#args) -> F {
                    #task_fn
                    task(#arg_values)
                }
            }

            static mut TASK: Option<::hyperloop::task::Task<inner::F>> = None;

            unsafe {
                if TASK.is_none() {
                    TASK = Some(::hyperloop::task::Task::new(inner::wrapper(#arg_values),
                                                             #priority));
                    Some(::core::pin::Pin::static_mut(TASK.as_mut().unwrap()).get_handle())
                } else {
                    None
                }
            }
        }
    };
    result.into()
}

struct Args {
    args: Punctuated<Expr, Token![,]>,
}

impl Parse for Args {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        match Punctuated::<Expr, Token![,]>::parse_terminated(input) {
            Ok(args) => Ok(Self { args }),
            Err(err) => Err(err),
        }
    }
}

/// Macro for creating a static allocator
///
/// Returns an [`ExecutorHandle`]
///
/// # Example
/// ```ignore
/// let mut executor = static_executor!(some_task(), another_task());
/// ```
#[proc_macro]
pub fn static_executor(tokens: TokenStream) -> TokenStream {
    let args = syn::parse_macro_input!(tokens as Args).args;

    let n_tasks = args.len();

    let result = quote! {
        {
            static mut EXECUTOR: Option<::hyperloop::executor::Executor<#n_tasks>> = None;
            let args = [#args];

            let executor = unsafe {
                EXECUTOR.get_or_insert(::hyperloop::executor::Executor::new(args))
            };

            ::core::pin::Pin::static_mut(executor).get_handle()
        }
    };

    result.into()
}
