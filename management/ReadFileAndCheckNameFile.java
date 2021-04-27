package management;

public interface ReadFileAndCheckNameFile extends ReadFile {
	//@ public model instance String nameFile;

	//@ ensures \result == nameFile.equals("valid");
	public /*@ pure @*/ boolean isValidFile();
}