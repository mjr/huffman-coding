package management;

import java.util.HashMap;
import java.util.Map;

public class Extractor {
    private String text;
    private Map<String, Character> codingTable;

    public void extract(String fileCompressedFile, String fileCodingTable, String fileWrite) {
        this.readFileCodingTable(fileCodingTable);

        this.readFileCompressedFile(fileCompressedFile);

        this.writeFile(fileWrite);
    }

    private void readFileCodingTable(String fileCodingTable) {
        System.out.println("READ " + fileCodingTable);
        File fileRead = File.read(fileCodingTable);
        this.createCodingTable(fileRead.getText());
    }

    private void readFileCompressedFile(String fileCompressedFile) {
        System.out.println("READ " + fileCompressedFile);
        File fileCompressedRead = File.read(fileCompressedFile);
        this.text = fileCompressedRead.getText();
    }

    private void writeFile(String fileWrite) {
        String temp = "";
        String result = "";
        for (int i = 0; i < this.text.length(); i++) {
            temp += this.text.charAt(i);

            if (this.codingTable.containsKey(temp)) {
                result += this.codingTable.get(temp);
                temp = "";
            }
        }

        System.out.println("WRITE " + fileWrite);
        File.write(fileWrite, result);
    }

    private void createCodingTable(String data) {
        Map<String, Character> result = new HashMap<>();

        String[] arrOfStr = data.split("\n");

        for (String a: arrOfStr) {
            if (a.contains("-")) {
                result.put(a.substring(3), (char) Integer.parseInt(a.substring(0, 2)));
            } else {
                result.put(a.substring(1), a.charAt(0));
            }
        }
        this.codingTable = result;
    }
}
