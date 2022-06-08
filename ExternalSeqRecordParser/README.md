# External Record Sequence Parser

This small project provides a utility for parsing a sequence of records `[ a : Int, b : BOOLEAN ]`, computed externally and supplied as a log of newline-separated, comma-separated field-value pairs (see [examples](./examples)). This function can then be injected it into a TLA+ spec as a `CONSTANT`.

[ExternalSeqRecordParser.java](ExternalSeqRecordParser.java) defines the Java class `ExternalSeqRecordParser` containing the `ExSeqRcdParser` function which parses a log of newline-separated, comma-separated field-value pairs into a TLA+ function

[ExternalSeqRecordParser.tla](ExternalSeqRecordParser.tla) is a dummy declaration for the `ExSeqRcdParser` function which is overriden by the Java function of the same name
