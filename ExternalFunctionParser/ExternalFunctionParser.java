import tlc2.value.impl.*;
import tlc2.value.IValue;

import java.io.*;
import java.util.*;

public class ExternalFunctionParser {
  // @TLAPlusOperator(identifier = "ExternalFunctionParser", module = "ExternalFunctionParser")
  public static IValue ExFunParser(final StringValue absolutePath) throws IOException {
    BufferedReader br = new BufferedReader(new FileReader(absolutePath.val.toString()));
    List<Value> xyPairs = new ArrayList<>();
    try {
      String line = br.readLine();
      while (line != null) {
        // split string on seperator
        String[] lnarr = line.split(", ");
        // [xyPairs] will hold the tuple of input and output values
        List<Value> xyPair = new ArrayList<>();
        xyPair.add(IntValue.gen(Integer.parseInt(lnarr[0])));
        xyPair.add(IntValue.gen(Integer.parseInt(lnarr[1])));
        // add the corresponding xyPair to the tuple of xyPairs
        xyPairs.add(new TupleValue(xyPair.toArray(new Value[0])));
        line = br.readLine();
      }
    } finally {
      br.close();
    }
    return new TupleValue(xyPairs.toArray(new Value[0]));
  }
}
