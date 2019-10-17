# Huffman Coding

A codificação de Huffman é um método de compressão que usa as probabilidades de ocorrência dos símbolos no conjunto de dados a ser comprimido para determinar códigos de tamanho variável para cada símbolo.

## Como executar?

### Para comprimir um arquivo.

```console
java -jar huffman-coding.jar compress arquivo.txt arquivo.edz arquivo.edt
```

### Para extrair um arquivo.

```console
java -jar huffman-coding.jar extract arquivo.edz arquivo.edt arquivo.txt
```
