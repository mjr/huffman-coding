package management;

public interface ReadFile {
  //@ public model instance String nameFileCompressed;

  //@ ensures \result == nameFileCompressed.isEmpty();
  public /*@ pure @*/ boolean isValidFile();

  public void readFile(String nameFile) throws NotFoundFileException;
}