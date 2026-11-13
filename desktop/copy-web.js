// Копирует файлы сайта из корня репозитория в desktop/dist — их и показывает приложение.
// Так сайт и приложение всегда работают на одном и том же коде.
const fs = require('fs');
const path = require('path');
const root = path.resolve(__dirname, '..');
const dist = path.join(__dirname, 'dist');
const files = ['index.html', 'style.css', 'app.js', 'ai-guide.js', 'manifest.webmanifest', 'icon.svg', 'icon-192.png', 'icon-512.png'];
fs.rmSync(dist, { recursive: true, force: true });
fs.mkdirSync(dist, { recursive: true });
for (const f of files) {
  const src = path.join(root, f);
  if (!fs.existsSync(src)) { console.error('Нет файла сайта: ' + f); process.exit(1); }
  fs.copyFileSync(src, path.join(dist, f));
}
console.log('Файлы сайта скопированы в desktop/dist: ' + files.length);
