package management;

public interface ReadFileAndCheckNameFile extends ReadFile {
    public /*@ pure @*/ boolean isValidFile();
}