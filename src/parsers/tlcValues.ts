import { Value, StructureValue, SetValue, SequenceValue, PrimitiveValue, StructureItem } from '../model/check';
import { ParsingError } from '../common';
import { Position } from 'vscode';

enum TokenType {
    Primitive,
    Name,
    SetStart,
    SetEnd,
    SequenceStart,
    SequenceEnd,
    StructureStart,
    StructureEnd,
    StructureItemSeparator,
    Comma,
    End
}

class Token {
    static END = new Token(TokenType.End, '');

    readonly type: TokenType;
    readonly str: string;

    constructor(type: TokenType, str: string) {
        this.type = type;
        this.str = str;
    }
}

/**
 * These tokens can be captured by comparing with constant strings.
 */
const CONST_TOKENS = [
    new Token(TokenType.SetStart, '{'),
    new Token(TokenType.SetEnd, '}'),
    new Token(TokenType.SequenceStart, '<<'),
    new Token(TokenType.SequenceEnd, '>>'),
    new Token(TokenType.StructureStart, '['),
    new Token(TokenType.StructureEnd, ']'),
    new Token(TokenType.StructureItemSeparator, '|->'),
    new Token(TokenType.Comma, ','),
];

/**
 * Breaks the given set of lines and allows to read them token-by-token.
 */
class Tokenizer {
    private lines: string[];
    private lineIdx: number = 0;
    private colIdx: number = 0;
    private position = new Position(0, 0);

    constructor(lines: string[]) {
        this.lines = lines;
        this.tryReadNumberToken = this.tryReadNumberToken.bind(this);
        this.tryReadStringToken = this.tryReadStringToken.bind(this);
        this.tryReadBooleanToken = this.tryReadBooleanToken.bind(this);
        this.tryReadNameToken = this.tryReadNameToken.bind(this);
    }

    nextToken(): Token {
        const str = this.nextStr();
        if (str == null) {
            return Token.END;
        }
        for (const token of CONST_TOKENS) {
            if (str.startsWith(token.str)) {
                this.colIdx += token.str.length;
                return token;
            }
        }
        const tokenFuncs = [
            this.tryReadNumberToken,
            this.tryReadStringToken,
            this.tryReadBooleanToken,
            this.tryReadNameToken
        ];
        for (const func of tokenFuncs) {
            const token = func(str);
            if (token != null) {
                return token;
            }
        }
        throw new ParsingError(`Cannot parse variable value at ${this.getPosition()}: ${str}`);
    }

    getPosition(): string {
        return `line ${this.position.line}, column ${this.position.character}`;
    }

    /**
     * Finds next piece of string to be parsed.
     * The resulting string must not be empty or start with space.
     */
    private nextStr(): string | null {
        while (this.lineIdx < this.lines.length) {
            const line = this.lines[this.lineIdx];
            while (this.colIdx < line.length && line[this.colIdx] === ' ') {
                this.colIdx += 1;
            }
            if (this.colIdx === line.length) {
                this.lineIdx += 1;
                this.colIdx = 0;
                continue;
            }
            this.position = new Position(this.lineIdx + 1, this.colIdx + 1);
            return line.substring(this.colIdx);
        }
        this.position = new Position(this.lines.length, this.lines[this.lines.length - 1].length);
        return null;
    }

    private tryReadStringToken(str: string): Token | null {
        if (!str.startsWith('"')) {
            return null;
        }
        let i = 1;
        let escape = false;
        while (i < str.length) {
            if (!escape) {
                const ch = str[i];
                if (ch === '\\') {
                    escape = true;
                } else if (ch === '"') {
                    this.colIdx += i + 1;
                    return new Token(TokenType.Primitive, str.substring(0, i + 1));
                }
            } else {
                escape = false;
            }
            i += 1;
        }
        throw new ParsingError(`Unexpected end of line while parsing string t ${this.getPosition()}`);
    }

    private tryReadNumberToken(str: string): Token | null {
        return this.tryRegexpToken(str, /^(-?\d+)/g, TokenType.Primitive);
    }

    private tryReadBooleanToken(str: string): Token | null {
        return this.tryRegexpToken(str, /^(TRUE|FALSE)/g, TokenType.Primitive);
    }

    private tryReadNameToken(str: string): Token | null {
        return this.tryRegexpToken(str, /^(\w+)/g, TokenType.Name);
    }

    private tryRegexpToken(str: string, regexp: RegExp, type: TokenType): Token | null {
        const matches = regexp.exec(str);
        if (matches) {
            this.colIdx += matches[1].length;
            return new Token(type, matches[1]);
        }
        return null;
    }
}

/**
 * Parses a set of lines that contain a variable value.
 * It's assumed that the given set of lines came from a TLC output, which means they follow
 * certain simple rules, like no line breaks in the middle of a token, etc.
 */
export function parseValueLines(lines: string[]): Value {
    const tokenizer = new Tokenizer(lines);
    try {
        return parseValue(tokenizer.nextToken(), tokenizer);
    } catch (err) {
        console.log('Error parsing variable value: ' + err);
        return new PrimitiveValue(lines.join(' '));
    }
}

function parseValue(token: Token, tokenizer: Tokenizer): Value {
    if (token.type === TokenType.End) {
        throw new ParsingError(`Unexpected end while parsing variable value at ${tokenizer.getPosition()}`);
    }
    if (token.type === TokenType.Primitive) {
        return new PrimitiveValue(token.str);
    }
    if (token.type === TokenType.SetStart) {
        const values = parseCollectionValues(tokenizer, TokenType.SetEnd, parseValue);
        return new SetValue(values);
    }
    if (token.type === TokenType.SequenceStart) {
        const values = parseCollectionValues(tokenizer, TokenType.SequenceEnd, parseValue);
        return new SequenceValue(values);
    }
    if (token.type === TokenType.StructureStart) {
        const values = parseCollectionValues(tokenizer, TokenType.StructureEnd, parseStructureItem);
        return new StructureValue(values);
    }
    throw new ParsingError(`Unexpected token at ${tokenizer.getPosition()}: ${token.str}`);
}

function parseStructureItem(token: Token, tokenizer: Tokenizer): StructureItem {
    if (token.type !== TokenType.Name) {
        throw new ParsingError(`Expected structure item at ${tokenizer.getPosition()}, found ${token.str}`);
    }
    const nextToken = tokenizer.nextToken();
    if (nextToken.type !== TokenType.StructureItemSeparator) {
        throw new ParsingError(`Expected structure item separator at ${tokenizer.getPosition()}, found ${token.str}`);
    }
    const value = parseValue(tokenizer.nextToken(), tokenizer);
    return new StructureItem(token.str, value);
}

function parseCollectionValues<T>(
    tokenizer: Tokenizer,
    endTokenType: TokenType,
    valueParser: (token: Token, tokenizer: Tokenizer) => T
): T[] {
    const values = [];
    let canClose = true;
    let canComma = false;
    while (true) {
        const token = tokenizer.nextToken();
        if (token.type === endTokenType) {
            if (!canClose) {
                throw new ParsingError(
                    `Unexpected end of collection at ${tokenizer.getPosition()}: ${token.str}`);
            }
            return values;
        }
        if (token.type === TokenType.Comma) {
            if (!canComma) {
                throw new ParsingError(
                    `Unexpected comma at ${tokenizer.getPosition()}: ${token.str}`);
            }
            canComma = false;
            canClose = false;
        } else {
            values.push(valueParser(token, tokenizer));
            canClose = true;
            canComma = true;
        }
    }
}
