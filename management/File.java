package management;

import java.io.*;
import java.nio.charset.StandardCharsets;

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
        BufferedReader fis = null;
        String text = "";
        try {
            Reader reader = new InputStreamReader(new FileInputStream(file), StandardCharsets.UTF_8);
            fis = new BufferedReader(reader);

            int content;
            while ((content = fis.read()) != -1) {
                if ((int) content < 256) {
                    text += (char) content;
                }
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

    public static File readByte(String pathname) {
        java.io.File file = new java.io.File(pathname);
        FileInputStream in = null;
        String text = "";
        try {
            in = new FileInputStream(pathname);
            byte[] bytes = in.readAllBytes();

            StringBuilder sb = new StringBuilder();
            int i = 0;
            for (; i < Byte.SIZE * bytes.length; i++) {
                sb.append(((bytes[i / Byte.SIZE] & (1 << (i % Byte.SIZE))) != 0) ? '1' : '0');
            }

            text = sb.toString();
        } catch (IOException e) {
            e.printStackTrace();
        } finally {
            try {
                if (in != null)
                    in.close();
            } catch (IOException ex) {
                ex.printStackTrace();
            }
        }

        return new File(file.length(), text);
    }

    public static File readExtract(String pathname) {
        java.io.File file = new java.io.File(pathname);
        BufferedReader fis = null;
        String text = "";
        try {
            Reader reader = new InputStreamReader(new FileInputStream(file), StandardCharsets.UTF_8);
            fis = new BufferedReader(reader);

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

    public static File write(String pathname, byte[] content) {
        java.io.File file = new java.io.File(pathname);
        FileOutputStream fos = null;

        try {
            fos = new FileOutputStream(file);
            fos.write(content);
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
}
