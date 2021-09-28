import tlc2.value.impl.*;

import java.io.*;
import java.util.*;

public class Parser {
  public static Value parser(final StringValue absolutePath) throws IOException {
    BufferedReader br = new BufferedReader(new FileReader(absolutePath.val.toString()));
    List<Value> values = new ArrayList<>();
    try {
      String line = br.readLine();
      while (line != null) {
        String[] lnarr = line.split(", ");
        List<Value> vals = new ArrayList<>();
        vals.add(IntValue.gen(Integer.parseInt(lnarr[0])));
        vals.add(new BoolValue(Boolean.parseBoolean(lnarr[1])));
        values.add(new TupleValue(vals.toArray(new Value[0])));
        line = br.readLine();
      }
    } finally {
      br.close();
    }
    return new TupleValue(values.toArray(new Value[0]));
  }
}
