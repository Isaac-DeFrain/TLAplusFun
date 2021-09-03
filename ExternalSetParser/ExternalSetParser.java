import tlc2.value.impl.*;
import util.UniqueString;

import java.io.*;
import java.util.*;

public class ExternalSetParser {
  public static Value ExSetParser(final StringValue absolutePath) throws IOException {
    // read the log file at [absolutePath]
    BufferedReader br = new BufferedReader(new FileReader(absolutePath.val.toString()));
    // initialize array for set of values
    List<Value> set = new ArrayList<>();
    try {
      String line = br.readLine();
      while (line != null) {
        // split string on seperator into array of elements
        String[] lnarr = line.split(", ");
        for (int i = 0; i < lnarr.length; i++) {
          // parse each entry of [lnarr] as a value of the appropriate type
          if (lnarr[i].equals("false") || lnarr[i].equals("true")) {
            set.add(new BoolValue(Boolean.parseBoolean(lnarr[i])));
          } else {
            try {
              IntValue x = IntValue.gen(Integer.parseInt(lnarr[i]));
              set.add(x);
            }
            catch (RuntimeException e) {
              set.add(new StringValue(lnarr[i]));
            }
          }
        }
        // read the next line
        line = br.readLine();
      }
    } finally {
      br.close();
    }
    // return the aggregated sequence of records
    return new SetEnumValue(set.toArray(new Value[0]), true);
  }
}
