# ExternalSetParser

Currently, this utility only parses comma-separated sequences of booleans, integers, and strings. It is meant to serve as blueprint for parsing sets with more complex elements.

An interesting discovery I made while testing this utility is that we must declare the returned set as *normalized* (see [return](./ExternalSetParser.java#L39)). If it is declared as unnormalized, then TLC can throw an error while comparing elements of different types.
