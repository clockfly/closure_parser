package spark.closure_poc;
/**
 * Created by seanzhong on 7/10/16.
 */
public class Map2 implements spark.closure_poc.MapFunction<Integer, Integer> {
  int c = 44;
  public Integer call(Integer a) {
    return 44;
  }
}
