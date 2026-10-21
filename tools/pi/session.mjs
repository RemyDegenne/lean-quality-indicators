// Isolated pi session: no discovered resources, only the shared Python source tools.
import { spawn } from "node:child_process";
import { readFileSync, mkdtempSync, rmSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { createInterface } from "node:readline";
import {
  createAgentSession, createExtensionRuntime, ModelRuntime, SessionManager, SettingsManager,
} from "@earendil-works/pi-coding-agent";

const version = JSON.parse(readFileSync(new URL("./node_modules/@earendil-works/pi-coding-agent/package.json", import.meta.url))).version;
if (process.env.ZAI_API_KEY_FILE) {
  process.env.ZAI_API_KEY = readFileSync(process.env.ZAI_API_KEY_FILE, "utf8").trim();
}
const runtime = await ModelRuntime.create({ modelsPath: null, allowModelNetwork: false });
if (process.argv[2] === "--check") {
  const [, , , provider, id] = process.argv;
  const model = runtime.getModel(provider, id);
  if (!model) throw new Error(`Unknown pi model ${provider}/${id}`);
  console.log(JSON.stringify({ version, provider, model: model.id,
    authenticated: Boolean(await runtime.getAuth(model)) }));
  process.exit(0);
}

let input = "";
for await (const chunk of process.stdin) input += chunk;
const config = JSON.parse(input);
const model = runtime.getModel(config.provider, config.model);
if (!model) throw new Error(`Unknown pi model ${config.provider}/${config.model}`);
if (!config.dry_run && !await runtime.getAuth(model)) throw new Error("Missing pi provider credentials");
const agentDir = mkdtempSync(join(tmpdir(), "lean-pi-judge-"));
const server = spawn(config.python, [config.source_server, ...config.roots], { stdio: ["pipe", "pipe", "inherit"] });
const pending = new Map();
let sequence = 0;
createInterface({ input: server.stdout }).on("line", (line) => {
  const reply = JSON.parse(line), waiter = pending.get(reply.id);
  if (waiter) {
    pending.delete(reply.id);
    reply.error ? waiter.reject(new Error(JSON.stringify(reply.error))) : waiter.resolve(reply.result);
  }
});
server.on("exit", () => {
  for (const waiter of pending.values()) waiter.reject(new Error("Source server exited"));
  pending.clear();
});
function rpc(method, params = {}) {
  return new Promise((resolve, reject) => {
    const id = ++sequence;
    pending.set(id, { resolve, reject });
    server.stdin.write(JSON.stringify({ jsonrpc: "2.0", id, method, params }) + "\n");
  });
}
let session;
try {
  const specs = (await rpc("tools/list")).tools;
  const names = ["Read", "Grep", "Glob"];
  const customTools = specs.map((spec) => ({ name: spec.name, label: spec.name,
    description: spec.description, parameters: spec.inputSchema,
    execute: async (_id, args) => ({ ...await rpc("tools/call", { name: spec.name, arguments: args }), details: {} }),
  }));
  const resourceLoader = {
    getExtensions: () => ({ extensions: [], errors: [], runtime: createExtensionRuntime() }),
    getSkills: () => ({ skills: [], diagnostics: [] }),
    getPrompts: () => ({ prompts: [], diagnostics: [] }),
    getThemes: () => ({ themes: [], diagnostics: [] }),
    getAgentsFiles: () => ({ agentsFiles: [] }),
    getSystemPrompt: () => config.prompt,
    getSystemPromptSource: () => undefined,
    getAppendSystemPrompt: () => [], getAppendSystemPromptSources: () => [],
    extendResources: () => {}, reload: async () => {},
  };
  ({ session } = await createAgentSession({ cwd: config.cwd, agentDir,
    model, modelRuntime: runtime, thinkingLevel: config.effort,
    resourceLoader, tools: names, customTools,
    sessionManager: SessionManager.inMemory(config.cwd),
    settingsManager: SettingsManager.inMemory({ compaction: { enabled: false }, retry: { enabled: false } }),
  }));
  if (JSON.stringify(session.getActiveToolNames().sort()) !== JSON.stringify(names.sort())) {
    throw new Error("Unexpected active tools");
  }
  if (config.dry_run) {
    const inside = await rpc("tools/call", { name: "Read", arguments: { path: config.test_file } });
    const outside = await rpc("tools/call", { name: "Read", arguments: { path: "/etc/passwd" } });
    if (inside.isError || !outside.isError || !session.systemPrompt.includes(config.prompt)) throw new Error("Isolation check failed");
    console.log(JSON.stringify({ type: "isolation_check", tools: session.getActiveToolNames(), outside_denied: true }));
  } else {
    session.subscribe((event) => {
      // Persist completed messages/tool activity, without copying auth/request headers.
      if (["message_end", "tool_execution_end"].includes(event.type)) console.log(JSON.stringify(event));
    });
    await session.prompt(config.message + "\n\nReturn only a JSON object matching this schema:\n" + JSON.stringify(config.schema));
    const messages = session.messages.filter((m) => m.role === "assistant");
    if (messages.some((m) => m.stopReason === "error" || m.stopReason === "aborted")) throw new Error(messages.at(-1).errorMessage || "Pi model request failed");
    const usage = messages.map((m) => m.usage);
    console.log(JSON.stringify({ type: "judge_result", text: session.getLastAssistantText(),
      turns: messages.length, usage, cost_usd: usage.reduce((s, u) => s + (u?.cost?.total || 0), 0) }));
  }
} finally {
  session?.dispose();
  server.kill();
  rmSync(agentDir, { recursive: true, force: true });
}
