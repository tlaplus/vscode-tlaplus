import * as fs from "fs/promises";
import { inflateRawSync } from "zlib";

const EOCD_SIGNATURE = 0x06054b50;
const CENTRAL_DIRECTORY_SIGNATURE = 0x02014b50;
const LOCAL_FILE_HEADER_SIGNATURE = 0x04034b50;

const MAX_EOCD_SEARCH = 1024 * 64; // 64KB from EOF

export async function readZipEntry(
  zipPath: string,
  entryPath: string,
): Promise<Buffer | undefined> {
  const normalizedEntry = entryPath.replace(/\\/g, "/");
  const data = await fs.readFile(zipPath);

  const eocdOffset = findEndOfCentralDirectory(data);
  if (eocdOffset < 0) {
    return undefined;
  }

  const centralDirectoryOffset = data.readUInt32LE(eocdOffset + 16);
  let ptr = centralDirectoryOffset;

  while (ptr < data.length - 46) {
    const signature = data.readUInt32LE(ptr);
    if (signature !== CENTRAL_DIRECTORY_SIGNATURE) {
      break;
    }

    const fileNameLength = data.readUInt16LE(ptr + 28);
    const extraLength = data.readUInt16LE(ptr + 30);
    const commentLength = data.readUInt16LE(ptr + 32);
    const compressedSize = data.readUInt32LE(ptr + 20);
    const localHeaderOffset = data.readUInt32LE(ptr + 42);
    const fileName = data
      .subarray(ptr + 46, ptr + 46 + fileNameLength)
      .toString("utf8");

    if (fileName === normalizedEntry) {
      return extractEntry(
        data,
        localHeaderOffset,
        compressedSize,
      );
    }

    ptr += 46 + fileNameLength + extraLength + commentLength;
  }

  return undefined;
}

function findEndOfCentralDirectory(buffer: Buffer): number {
  const searchLength = Math.min(MAX_EOCD_SEARCH, buffer.length);
  for (let i = buffer.length - 22; i >= buffer.length - searchLength; i--) {
    if (i < 0) {
      break;
    }
    if (buffer.readUInt32LE(i) === EOCD_SIGNATURE) {
      return i;
    }
  }
  return -1;
}

function extractEntry(
  buffer: Buffer,
  localHeaderOffset: number,
  compressedSize: number,
): Buffer | undefined {
  if (buffer.readUInt32LE(localHeaderOffset) !== LOCAL_FILE_HEADER_SIGNATURE) {
    return undefined;
  }

  const compressionMethod = buffer.readUInt16LE(localHeaderOffset + 8);
  const fileNameLength = buffer.readUInt16LE(localHeaderOffset + 26);
  const extraLength = buffer.readUInt16LE(localHeaderOffset + 28);
  const dataStart =
    localHeaderOffset + 30 + fileNameLength + extraLength;
  const compressedData = buffer.subarray(
    dataStart,
    dataStart + compressedSize,
  );

  if (compressionMethod === 0) {
    return Buffer.from(compressedData);
  }

  if (compressionMethod === 8) {
    return inflateRawSync(compressedData);
  }

  return undefined;
}
