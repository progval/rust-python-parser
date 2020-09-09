# v0.2.0

work in progress

Support for 3.8 syntax

Breaking changes:

* Added `Expression::Await` variant
* Added `Expression::Named` variant
* Changed TypedArgsList and UntypedArgsList to add `posonly_args` field, and rename `positional_args` to `args`

Other changes

* Minor bug fixes (see git history)
* `cargo fmt`
* Make the dependency on `unicode_names2` optional.

# v0.1.0

Initial release, with support for 3.7 syntax
