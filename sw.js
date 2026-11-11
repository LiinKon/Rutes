// Офлайн-кэш приложения отключён: программа всегда грузится свежей с GitHub.
// Этот файл только убирает старый кэш у тех, кто открывал прошлые версии, и отключает сам себя.
// Доски хранятся отдельно (IndexedDB) и не затрагиваются.
self.addEventListener('install', () => self.skipWaiting());
self.addEventListener('activate', e => e.waitUntil((async () => {
  for (const k of await caches.keys()) await caches.delete(k);
  await self.registration.unregister();
  for (const c of await self.clients.matchAll({ type: 'window' })) c.navigate(c.url);
})()));
