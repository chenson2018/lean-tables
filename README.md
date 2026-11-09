# Brown Benchmark for Table Types in Lean

This project is an implementation of the [Brown Benchmark for Table Types (B2T2)](https://github.com/brownplt/B2T2) in Lean 4. Further documentation is forthcoming; in the meantime, refer to the [B2T2 API specification](https://github.com/brownplt/B2T2/blob/main/TableAPI.md).

The project uses Lean and Mathlib `v4.36.0-rc2`. Shared definitions such as `Function.swap` and `List.product` come from Mathlib and its dependencies. The test suite checks that the table library can be imported together with the full `Mathlib` module.

To fetch the precompiled Mathlib dependencies, build the library, and run the tests:

```sh
lake exe cache get
lake build
lake test
```

The assertion command in `Tests.TestingNotation` is `#table_test`; Mathlib's `#test` command remains available for Plausible tests.
