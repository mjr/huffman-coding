package management;

import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.IOException;
import java.util.BitSet;

public class File {
    private long size;
    private String text;

    public File(long size) {
        this.size = size;
    }

    public File(long size, String text) {
        this.size = size;
        this.text = text;
    }

    public long getSize() {
        return size;
    }

    public String getText() {
        return text;
    }

    public static File read(String pathname) {
        java.io.File file = new java.io.File(pathname);
        FileInputStream fis = null;
        String text = "";
        try {
            fis = new FileInputStream(file);

            // System.out.println("Total file size to read (in bytes) : " + fis.available());

            int content;
            while ((content = fis.read()) != -1) {
                text += (char) content;
            }
        } catch (IOException e) {
            e.printStackTrace();
        } finally {
            try {
                if (fis != null)
                    fis.close();
            } catch (IOException ex) {
                ex.printStackTrace();
            }
        }
        return new File(file.length(), text);
    }

    public static File write(String pathname, String content) {
        java.io.File file = new java.io.File(pathname);
        FileOutputStream fos = null;

        try {
            fos = new FileOutputStream(file);

            // System.out.println("Total file size to read (in bytes) : " + fos.available());

            byte[] bytes = content.getBytes();
            fos.write(bytes);
        } catch (IOException e) {
            e.printStackTrace();
        } finally {
            try {
                if (fos != null)
                    fos.close();
            } catch (IOException ex) {
                ex.printStackTrace();
            }
        }

        return new File(file.length());
    }

    public static void writeInBytes(String pathname, String content, BitSet bits) {
        java.io.File file = new java.io.File(pathname);
        FileOutputStream oos = null;

        try {
            oos = new FileOutputStream(file);

            // System.out.println("Total file size to read (in bytes) : " + bos.available());

            // byte[] bytes = content.getBytes();
            oos.write(bits.toByteArray());
        } catch (IOException e) {
            e.printStackTrace();
        } finally {
            try {
                if (oos != null)
                    oos.close();
            } catch (IOException ex) {
                ex.printStackTrace();
            }
        }
    }
}
