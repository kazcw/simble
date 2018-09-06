# Simble

Simple, tiny symbols. Human-readable strings up to 8 bytes long that can be
stored inline and manipulated efficiently.

### Why would I want this?

If:
- you are working with human-readable strings that never exceed 8 bytes
- the set of strings is not fixed at compile time, so you can't use an `enum`

Then Simble offers:
- efficient storage
- fast comparisons and hashing

### Optional features

- `serde`: `Lexical` and `Printable` both serialize/deserialize like a
  restricted String

### Current nightly features

Enable with the `nightly` feature:

- const fns, so that you can define symbols that will be parsed at compile time
