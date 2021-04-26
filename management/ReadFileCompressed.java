package management;

public interface ReadFileCompressed {
  //@ public model instance String nameFileCompressed;

  //@ ensures \result == nameFileCompressed.isEmpty();
  public /*@ pure @*/ boolean isValidFile();

  public void readFileCompressedFile(String fileCompressedFile) throws NotFoundFileException;
}