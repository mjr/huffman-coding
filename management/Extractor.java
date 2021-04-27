package management;

import java.util.HashMap;
import java.util.Map;

public class Extractor implements ReadFileAndCheckNameFile {
    private String text;
    private Map<String, Character> codingTable;
    private /*@ spec_public @*/ String result = "";
    private String nameFile;

    /*@
  	@ requires fileCompressedFile != "";
  	@ requires fileCodingTable != ";
  	@ requires fileWrite != ";
  	@*/
    public void extract(String fileCompressedFile, String fileCodingTable, String fileWrite) throws InvalidFileException {
        this.nameFile = fileCompressedFile;

        if (!this.isValidFile()) {
        	throw new InvalidFileException("Arquivo inválido!");
        }

        this.readFileCodingTable(fileCodingTable);

        this.readFile(fileCompressedFile);

        this.setResult();

        this.writeFile(fileWrite);
    }

    /*@
  	@ ensures result != "";
  	@*/
    public void setResult() {
        String temp = "";
        for (int i = 0; i < this.text.length(); i++) {
            temp += this.text.charAt(i);

            if (this.codingTable.containsKey(temp)) {
                int tempResult = (int) this.codingTable.get(temp);
                if (tempResult == 65526) {
                    return;
                }

                this.result += this.codingTable.get(temp);
                temp = "";
            }
        }
    }

    public /*@ pure @*/ boolean isValidFile() {
        return !this.nameFile.isEmpty();
    }

    private void readFileCodingTable(String fileCodingTable) {
        File fileRead = File.readExtract(fileCodingTable);
        this.createCodingTable(fileRead.getText());
    }

    public void readFile(String fileCompressedFile) {
        File fileCompressedRead = File.readByte(fileCompressedFile);
        this.text = fileCompressedRead.getText();
    }

    private void writeFile(String fileWrite) {
        File.write(fileWrite, this.result.getBytes());
    }

    private void createCodingTable(String data) {
        Map<String, Character> result = new HashMap<>();

        String[] arrOfStr = data.split("\n");

        for (String a: arrOfStr) {
            if (a.substring(1).contains("-")) {
                result.put(a.substring(3), (char) Integer.parseInt(a.substring(0, 2)));
            } else {
                result.put(a.substring(1), a.charAt(0));
            }
        }
        this.codingTable = result;
    }
}