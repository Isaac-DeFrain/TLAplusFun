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
        vals.add(new StringValue(lnarr[0]));
        vals.add(parseData(lnarr[0], tail(lnarr)));
        values.add(new TupleValue(vals.toArray(new Value[0])));
        line = br.readLine();
      }
    } finally {
      br.close();
    }
    return new TupleValue(values.toArray(new Value[0]));
  }

  private static Value parseData(String action, String[] data) {
    Value ret;
    if (action.equals("Count_A")) {
      ret = parseCountAData(data);
    } else if (action.equals("Switch_A")) {
      ret = parseSwitchAData(data);
    } else {
      ret = new TupleValue(new ArrayList<>().toArray(new Value[0]));
    }
    return ret;
  }

  private static Value parseCountAData(String[] data) {
    if (data.length != 2) {
      throw new IllegalArgumentException("Count_A data needs two values");
    }
    List<Value> vals = new ArrayList<>();
    vals.add(new BoolValue(Boolean.parseBoolean(data[0])));
    vals.add(IntValue.gen(Integer.parseInt(data[1])));
    return new TupleValue(vals.toArray(new Value[0]));
  }

  private static Value parseSwitchAData(String[] data) {
    if (data.length != 1) {
      throw new IllegalArgumentException("Switch_A data needs one value");
    }
    List<Value> vals = new ArrayList<>();
    vals.add(IntValue.gen(Integer.parseInt(data[0])));
    return new TupleValue(vals.toArray(new Value[0]));
  }

  private static <T> T[] tail(T[] array) {
    int len = array.length;
    if (len == 0) {
      throw new IllegalArgumentException("Array cannot be empty");
    }
    return Arrays.copyOfRange(array, 1, len);
  }
}
