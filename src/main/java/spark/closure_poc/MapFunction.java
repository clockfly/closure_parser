package spark.closure_poc;

public interface MapFunction<T, U> extends java.io.Serializable {
  U call(T value) throws Exception;
}