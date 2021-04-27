import management.Extractor;
import management.Compressor;
import management.InvalidFileException;

public class Main {
    public static void main(String[] args) throws InvalidFileException {
        if (args[0].equals("compress")) {
            Compressor compressor = new Compressor();
            compressor.compress(args[1], args[2], args[3]);
        } else if (args[0].equals("extract")) {
            Extractor extractor = new Extractor();
            extractor.extract(args[1], args[2], args[3]);
        } else {
            System.out.println("Operação Inválida!");
        }
        System.out.println("Finished!");
    }
}
