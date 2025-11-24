import * as assert from 'assert';
import * as fs from 'fs';
import * as path from 'path';
import * as vscode from 'vscode';
import { MCPServer } from '../../../src/lm/MCPServer';
import { McpServer as SdkMcpServer } from '@modelcontextprotocol/sdk/server/mcp.js';

const fsp = fs.promises;

suite('MCP Server Knowledge Base', () => {
    let tempDir: string;
    let tempKnowledgeBaseDir: string;
    let originalExtension: vscode.Extension<any> | undefined;
    let originalGetExtension: typeof vscode.extensions.getExtension;

    suiteSetup(async () => {
        // Create temporary directory for test files
        tempDir = await fsp.mkdtemp(path.join(__dirname, 'mcp-kb-test-'));
        tempKnowledgeBaseDir = path.join(tempDir, 'knowledgebase');
        await fsp.mkdir(tempKnowledgeBaseDir, { recursive: true });

        // Store the original getExtension method for restoration
        originalGetExtension = vscode.extensions.getExtension;

        // Mock the extension to return our temp directory
        originalExtension = vscode.extensions.getExtension('tlaplus.vscode-ide');
        const mockExtension = {
            extensionPath: tempDir,
            id: 'tlaplus.vscode-ide',
            extensionUri: vscode.Uri.file(tempDir),
            isActive: true,
            packageJSON: {},
            exports: undefined,
            activate: async () => undefined
        };
        
        // Override the getExtension method
        vscode.extensions.getExtension = (extensionId: string) => {
            if (extensionId === 'tlaplus.vscode-ide') {
                return mockExtension as any;
            }
            return originalGetExtension.call(vscode.extensions, extensionId);
        };
    });

    suiteTeardown(async () => {
        // Restore the original getExtension method to prevent test pollution
        if (originalGetExtension) {
            vscode.extensions.getExtension = originalGetExtension;
        }
        
        // Clean up temp directory
        if (tempDir) {
            await fsp.rm(tempDir, { recursive: true, force: true });
        }
    });

    setup(async () => {
        // Create test knowledge base files before each test
        await createTestKnowledgeBaseFiles();
    });

    teardown(async () => {
        // Clean up knowledge base files after each test
        const files = await fsp.readdir(tempKnowledgeBaseDir);
        await Promise.all(files.map(file => 
            fsp.rm(path.join(tempKnowledgeBaseDir, file), { force: true })
        ));
    });

    async function createTestKnowledgeBaseFiles() {
        // Create test markdown files with different frontmatter structures
        const testFiles = [
            {
                name: 'test-article-1.md',
                content: `---
title: Test Article One
description: This is a test article about TLA+ basics
---

# Test Article One

This is the content of test article one.
It contains information about TLA+ specifications.

## Section 1

Some detailed content here.
`
            },
            {
                name: 'test-article-2.md',
                content: `---
title: Advanced TLA+ Concepts
description: Deep dive into advanced TLA+ features and patterns
---

# Advanced TLA+ Concepts

This article covers advanced topics.

## Advanced Features

- Temporal logic
- Model checking
- Refinement
`
            },
            {
                name: 'no-frontmatter.md',
                content: `# Article Without Frontmatter

This article has no frontmatter metadata.
The title should be derived from the filename.
`
            },
            {
                name: 'partial-frontmatter.md',
                content: `---
title: Article with Partial Frontmatter
---

# Partial Frontmatter Article

This article only has a title in frontmatter.
`
            },
            {
                name: 'search-test.md',
                content: `---
title: Searchable Article
description: Contains searchable keywords
---

# Searchable Content

This article contains the word "nondeterminism" in its content.
It also discusses temporal logic and model checking.
`
            }
        ];

        for (const file of testFiles) {
            await fsp.writeFile(path.join(tempKnowledgeBaseDir, file.name), file.content);
        }
    }

    suite('MCP Resources Registration', () => {
        test('should register knowledge base resources correctly', async () => {
            const mcpServer = new MCPServer(0);
            try {
                // Get the internal server instance to check registered resources
                const serverInstance = await (mcpServer as any).getServer() as SdkMcpServer;
                
                // The resources should be registered during server creation
                // We can't directly access the registered resources, but we can test
                // that the registration process doesn't throw errors
                assert.ok(serverInstance, 'MCP server instance should be created');
                
                // Test that knowledge base directory exists and contains our test files
                const files = await fsp.readdir(tempKnowledgeBaseDir);
                const mdFiles = files.filter(f => f.endsWith('.md'));
                assert.strictEqual(mdFiles.length, 5, 'Should have 5 test markdown files');
                
            } finally {
                mcpServer.dispose();
            }
        });

        test('should handle missing knowledge base directory gracefully', async () => {
            // Temporarily rename the knowledge base directory to simulate it not existing
            const hiddenDir = tempKnowledgeBaseDir + '_hidden';
            await fsp.rename(tempKnowledgeBaseDir, hiddenDir);
            
            try {
                const mcpServer = new MCPServer(0);
                try {
                    // Should not throw an error even when knowledge base directory is missing
                    const serverInstance = await (mcpServer as any).getServer() as SdkMcpServer;
                    assert.ok(serverInstance, 'MCP server should still be created when KB directory is missing');
                } finally {
                    mcpServer.dispose();
                }
            } finally {
                // Restore the directory
                await fsp.rename(hiddenDir, tempKnowledgeBaseDir);
            }
        });
    });

    suite('Knowledge Base Tools', () => {
        let mcpServer: MCPServer;
        let serverInstance: SdkMcpServer;

        setup(async () => {
            // Enable knowledge base tools for testing
            await vscode.workspace.getConfiguration().update(
                'tlaplus.mcp.enableKnowledgeBaseTools', 
                true, 
                vscode.ConfigurationTarget.Global
            );
            
            mcpServer = new MCPServer(0);
            serverInstance = await (mcpServer as any).getServer() as SdkMcpServer;
        });

        teardown(() => {
            mcpServer?.dispose();
        });

        suite('tlaplus_mcp_knowledge_list tool', () => {
            test('should list all articles without search filter', async () => {
                const result = await (mcpServer as any).listKnowledgeArticles(
                    tempKnowledgeBaseDir,
                    ['test-article-1.md', 'test-article-2.md', 'no-frontmatter.md', 'partial-frontmatter.md', 'search-test.md']
                );

                assert.ok(result.content, 'Should return content');
                assert.strictEqual(result.content.length, 1, 'Should return single content item');
                
                const text = result.content[0].text;
                assert.ok(text.includes('Available TLA+ knowledge base articles (5 total)'), 'Should show total count');
                assert.ok(text.includes('Test Article One'), 'Should include first article title');
                assert.ok(text.includes('Advanced TLA+ Concepts'), 'Should include second article title');
                assert.ok(text.includes('no frontmatter'), 'Should include derived title for file without frontmatter');
                assert.ok(text.includes('Article with Partial Frontmatter'), 'Should include partial frontmatter title');
                assert.ok(text.includes('Searchable Article'), 'Should include searchable article');
            });

            test('should filter articles by search term in title', async () => {
                const result = await (mcpServer as any).listKnowledgeArticles(
                    tempKnowledgeBaseDir,
                    ['test-article-1.md', 'test-article-2.md', 'search-test.md'],
                    'Advanced'
                );

                const text = result.content[0].text;
                assert.ok(text.includes('Found 1 TLA+ knowledge base articles matching "Advanced"'), 'Should show filtered count');
                assert.ok(text.includes('Advanced TLA+ Concepts'), 'Should include matching article');
                assert.ok(!text.includes('Test Article One'), 'Should not include non-matching article');
            });

            test('should filter articles by search term in description', async () => {
                const result = await (mcpServer as any).listKnowledgeArticles(
                    tempKnowledgeBaseDir,
                    ['test-article-1.md', 'search-test.md'],
                    'searchable keywords'
                );

                const text = result.content[0].text;
                assert.ok(text.includes('Found 1 TLA+ knowledge base articles matching'), 'Should show filtered results');
                assert.ok(text.includes('Searchable Article'), 'Should include article with matching description');
            });

            test('should filter articles by search term in content', async () => {
                const result = await (mcpServer as any).listKnowledgeArticles(
                    tempKnowledgeBaseDir,
                    ['test-article-1.md', 'search-test.md'],
                    'nondeterminism'
                );

                const text = result.content[0].text;
                assert.ok(text.includes('Found 1 TLA+ knowledge base articles matching'), 'Should show filtered results');
                assert.ok(text.includes('Searchable Article'), 'Should include article with matching content');
                assert.ok(!text.includes('Test Article One'), 'Should not include non-matching article');
            });

            test('should perform case-insensitive search', async () => {
                const result = await (mcpServer as any).listKnowledgeArticles(
                    tempKnowledgeBaseDir,
                    ['test-article-2.md'],
                    'ADVANCED'
                );

                const text = result.content[0].text;
                assert.ok(text.includes('Found 1 TLA+ knowledge base articles matching'), 'Should find article with case-insensitive search');
                assert.ok(text.includes('Advanced TLA+ Concepts'), 'Should include matching article');
            });

            test('should return empty results when no matches found', async () => {
                const result = await (mcpServer as any).listKnowledgeArticles(
                    tempKnowledgeBaseDir,
                    ['test-article-1.md', 'test-article-2.md'],
                    'nonexistent-term'
                );

                const text = result.content[0].text;
                assert.ok(text.includes('Found 0 TLA+ knowledge base articles matching'), 'Should show zero results');
                assert.ok(!text.includes('Use tlaplus_mcp_knowledge_get'), 'Should not show usage instructions for empty results');
            });
        });

        suite('tlaplus_mcp_knowledge_get tool', () => {
            test('should retrieve single article by name', async () => {
                const result = await (mcpServer as any).getKnowledgeArticles(
                    tempKnowledgeBaseDir,
                    ['test-article-1']
                );

                assert.ok(result.content, 'Should return content');
                const text = result.content[0].text;
                assert.ok(text.includes('# Test Article One'), 'Should include article title');
                assert.ok(text.includes('This is the content of test article one'), 'Should include article content');
                assert.ok(!text.includes('---'), 'Should not include frontmatter separators');
                assert.ok(!text.includes('title: Test Article One'), 'Should not include frontmatter content');
            });

            test('should retrieve article by name with .md extension', async () => {
                const result = await (mcpServer as any).getKnowledgeArticles(
                    tempKnowledgeBaseDir,
                    ['test-article-1.md']
                );

                const text = result.content[0].text;
                assert.ok(text.includes('# Test Article One'), 'Should retrieve article when .md extension is provided');
            });

            test('should retrieve multiple articles', async () => {
                const result = await (mcpServer as any).getKnowledgeArticles(
                    tempKnowledgeBaseDir,
                    ['test-article-1', 'test-article-2']
                );

                const text = result.content[0].text;
                assert.ok(text.includes('# Test Article One'), 'Should include first article');
                assert.ok(text.includes('# Advanced TLA+ Concepts'), 'Should include second article');
                assert.ok(text.includes('---'), 'Should separate articles with divider');
            });

            test('should handle article without frontmatter', async () => {
                const result = await (mcpServer as any).getKnowledgeArticles(
                    tempKnowledgeBaseDir,
                    ['no-frontmatter']
                );

                const text = result.content[0].text;
                assert.ok(text.includes('# Article Without Frontmatter'), 'Should include article content');
                assert.ok(text.includes('This article has no frontmatter metadata'), 'Should include full content');
            });

            test('should handle article with partial frontmatter', async () => {
                const result = await (mcpServer as any).getKnowledgeArticles(
                    tempKnowledgeBaseDir,
                    ['partial-frontmatter']
                );

                const text = result.content[0].text;
                assert.ok(text.includes('# Partial Frontmatter Article'), 'Should include article content');
                assert.ok(!text.includes('title: Article with Partial Frontmatter'), 'Should not include frontmatter');
            });

            test('should handle non-existent articles', async () => {
                const result = await (mcpServer as any).getKnowledgeArticles(
                    tempKnowledgeBaseDir,
                    ['non-existent-article']
                );

                const text = result.content[0].text;
                assert.ok(text.includes('**Articles not found:** non-existent-article'), 'Should list non-existent articles');
                assert.ok(text.includes('**Available articles'), 'Should list available articles when some not found');
            });

            test('should handle mixed results (some found, some not found)', async () => {
                const result = await (mcpServer as any).getKnowledgeArticles(
                    tempKnowledgeBaseDir,
                    ['test-article-1', 'non-existent', 'test-article-2']
                );

                const text = result.content[0].text;
                assert.ok(text.includes('# Test Article One'), 'Should include found articles');
                assert.ok(text.includes('# Advanced TLA+ Concepts'), 'Should include other found articles');
                assert.ok(text.includes('**Articles not found:** non-existent'), 'Should list not found articles');
                assert.ok(text.includes('**Available articles'), 'Should list available articles');
            });

            test('should validate article names and reject path traversal', async () => {
                const maliciousNames = [
                    '../../../etc/passwd',
                    '..\\..\\windows\\system32\\config\\sam',
                    'article/../secret',
                    'article/subdir/file'
                ];

                for (const maliciousName of maliciousNames) {
                    const result = await (mcpServer as any).getKnowledgeArticles(
                        tempKnowledgeBaseDir,
                        [maliciousName]
                    );

                    const text = result.content[0].text;
                    assert.ok(
                        text.includes('**Articles not found:**') && text.includes('Invalid article name'),
                        `Should reject malicious article name: ${maliciousName}`
                    );
                }
            });

            test('should handle empty article list', async () => {
                const result = await (mcpServer as any).getKnowledgeArticles(
                    tempKnowledgeBaseDir,
                    []
                );

                const text = result.content[0].text;
                assert.strictEqual(text, 'No articles found.', 'Should return appropriate message for empty list');
            });
        });

        suite('Frontmatter Parsing', () => {
            test('should parse complete frontmatter correctly', () => {
                const content = `---
title: Test Title
description: Test Description
---

# Content Here`;

                const metadata = (mcpServer as any).parseMarkdownFrontmatter(content);
                assert.strictEqual(metadata.title, 'Test Title', 'Should parse title correctly');
                assert.strictEqual(metadata.description, 'Test Description', 'Should parse description correctly');
            });

            test('should handle frontmatter with only title', () => {
                const content = `---
title: Only Title
---

# Content Here`;

                const metadata = (mcpServer as any).parseMarkdownFrontmatter(content);
                assert.strictEqual(metadata.title, 'Only Title', 'Should parse title correctly');
                assert.strictEqual(metadata.description, undefined, 'Should not have description');
            });

            test('should handle content without frontmatter', () => {
                const content = `# Just Content

No frontmatter here.`;

                const metadata = (mcpServer as any).parseMarkdownFrontmatter(content);
                assert.strictEqual(metadata.title, undefined, 'Should not have title');
                assert.strictEqual(metadata.description, undefined, 'Should not have description');
            });

            test('should handle malformed frontmatter', () => {
                const content = `---
title: Test Title
malformed line without colon
description: Test Description
---

# Content Here`;

                const metadata = (mcpServer as any).parseMarkdownFrontmatter(content);
                assert.strictEqual(metadata.title, 'Test Title', 'Should parse valid title');
                assert.strictEqual(metadata.description, 'Test Description', 'Should parse valid description');
            });
        });

        suite('Article Name Validation', () => {
            test('should accept valid article names', () => {
                const validNames = [
                    'tla-choose-nondeterminism',
                    'tla-diagnose-property-violations',
                    'simple-article',
                    'article_with_underscores',
                    'Article123',
                    'a',
                    'article.md'
                ];

                for (const name of validNames) {
                    assert.doesNotThrow(() => {
                        (mcpServer as any).validateArticleName(name);
                    }, `Should accept valid article name: ${name}`);
                }
            });

            test('should reject path traversal attempts', () => {
                const maliciousNames = [
                    '../../../etc/passwd',
                    '..\\..\\windows\\system32\\config\\sam',
                    'article/../../../secret.txt',
                    'article\\..\\..\\secret.txt',
                    '../article',
                    '..\\article',
                    'article/subdir/file',
                    'article\\subdir\\file'
                ];

                for (const name of maliciousNames) {
                    assert.throws(() => {
                        (mcpServer as any).validateArticleName(name);
                    }, /Invalid article name.*contains path/, `Should reject malicious name: ${name}`);
                }
            });

            test('should reject dangerous characters', () => {
                const dangerousNames = [
                    'article\x00null',  // null byte
                    'article<script>',
                    'article>redirect',
                    'article|pipe',
                    'article*wildcard',
                    'article?query',
                    'article"quote',
                    'article\'quote',
                    'article`backtick',
                    'article;semicolon',
                    'article:colon'
                ];

                for (const name of dangerousNames) {
                    assert.throws(() => {
                        (mcpServer as any).validateArticleName(name);
                    }, /Invalid article name.*contains (invalid characters|null byte)/, `Should reject dangerous name: ${name}`);
                }
            });

            test('should reject empty and invalid inputs', () => {
                const invalidInputs = [
                    '',
                    null as unknown as string,
                    undefined as unknown as string,
                    123 as unknown as string,
                    {} as unknown as string
                ];

                for (const input of invalidInputs) {
                    assert.throws(() => {
                        (mcpServer as any).validateArticleName(input);
                    }, /Article name must be a non-empty string/, `Should reject invalid input: ${input}`);
                }
            });

            test('should reject excessively long names', () => {
                const longName = 'a'.repeat(101);
                assert.throws(() => {
                    (mcpServer as any).validateArticleName(longName);
                }, /Invalid article name.*is too long/, 'Should reject names longer than 100 characters');

                const maxLengthName = 'a'.repeat(100);
                assert.doesNotThrow(() => {
                    (mcpServer as any).validateArticleName(maxLengthName);
                }, 'Should accept names exactly 100 characters long');
            });
        });
    });
});
