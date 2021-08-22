import tlc2.value.impl.*;

import java.io.*;
import java.util.*;

public class ExternalFunctionParser {
  // @TLAPlusOperator(identifier = "ExFunParser", module = "ExternalFunctionParser")
  public static Value ExFunParser(final StringValue absolutePath) throws IOException {
    BufferedReader br = new BufferedReader(new FileReader(absolutePath.val.toString()));
    List<IntValue> domain = new ArrayList<>();
    List<IntValue> values = new ArrayList<>();
    try {
      String line = br.readLine();
      while (line != null) {
        // split string on seperator
        String[] lnarr = line.split(", ");
        domain.add(IntValue.gen(Integer.parseInt(lnarr[0])));
        values.add(IntValue.gen(Integer.parseInt(lnarr[1])));
        line = br.readLine();
      }
    } finally {
      br.close();
    }
    return new FcnRcdValue(domain.toArray(new Value[0]), values.toArray(new Value[0]), true);
  }
}
