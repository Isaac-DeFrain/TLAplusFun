# External Functions

This small project provides a utility for parsing an `int -> int` function, computed externally and supplied as a log of comma-separated input-output values (see [examples](./examples)). This function can then be injected it into a TLA+ spec as a `CONSTANT`.

## `ExternalFunctionParser`

This module declares three operators:

`ExFunParser` - parses a log of input-output pairs into a TLA+ sequence of pairs through the Java override in [ExternalFunctionParser](./ExternalFunctionParser.java)

`SeqToFn` - recursive operator which converts the sequence of pairs into a TLA+ function

`parseFn` - composes the above operators
