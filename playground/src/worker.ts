import { lsp, ServerIo } from 'lsp-base'

let worker = self;

const encoder = new TextEncoder();
const decoder = new TextDecoder();

self.onmessage = (e) => console.log(e);

class Headers {
  static add(message: string): string {
    return `Content-Length: ${message.length}\r\n\r\n${message}`;
  }

  static remove(delimited: string): string {
    return delimited.replace(/^Content-Length:\s*\d+\s*/, "");
  }
}

let server_io = new ServerIo(
  new ReadableStream({
    start(controller) {
      worker.onmessage = (e) => {
        console.log('worker received', e.data); 
        controller.enqueue(encoder.encode(Headers.add(JSON.stringify(e.data))));
      };
    },
    type: 'bytes'
  }),
  new WritableStream({
    write(chunk) {
      let msg = JSON.parse(Headers.remove(decoder.decode(chunk)));
      console.log('worker sent', msg);
      worker.postMessage(msg)
    },
    close() {
      close()
    },
    abort(reason) {
      throw new Error(reason)
    },
  }));

console.log('launched lsp');
self.postMessage('ready')
await lsp(server_io);
