const CACHE_PREFIX = "school-system";
const CACHE_VERSION = "v50-backup-center";
const CACHE_NAME = `${CACHE_PREFIX}-${CACHE_VERSION}`;
const OFFLINE_URL = "/offline";
const PRIVATE_PREFIXES = ["/admin","/finance-dashboard","/teacher","/student","/parent","/librarian","/driver","/communication","/library","/online-classes","/e-learning","/notifications"];
const SHELL = ["/","/login","/static/css/style.css","/static/css/desktop.css","/static/css/mobile.css","/static/js/app.js","/static/manifest.json","/static/icons/icon-192.png","/static/icons/icon-512.png","/favicon.ico",OFFLINE_URL];
self.addEventListener("install", event => { event.waitUntil((async()=>{ const cache=await caches.open(CACHE_NAME); await Promise.all(SHELL.map(async url=>{try{await cache.add(url);}catch(_){}})); await self.skipWaiting(); })()); });
self.addEventListener("activate", event => { event.waitUntil((async()=>{ const keys=await caches.keys(); await Promise.all(keys.filter(k=>k.startsWith(`${CACHE_PREFIX}-`)&&k!==CACHE_NAME).map(k=>caches.delete(k))); await self.clients.claim(); })()); });
async function networkFirst(request){ const cache=await caches.open(CACHE_NAME); try{ const response=await fetch(request); if(response&&response.ok&&new URL(request.url).origin===self.location.origin){ await cache.put(request,response.clone()); } return response; } catch(_){ const cached=await cache.match(request); if(cached)return cached; if(request.mode==="navigate") { const cachedExact=await cache.match(request); if(cachedExact)return cachedExact; return (await cache.match(OFFLINE_URL)) || (await cache.match("/login")) || Response.error(); } return Response.error(); } }
self.addEventListener("fetch", event => {
  const request = event.request;
  if(request.method !== "GET") return;
  const url = new URL(request.url);
  const isPrivate = PRIVATE_PREFIXES.some(p=>url.pathname===p || url.pathname.startsWith(p+"/"));
  if(url.origin !== self.location.origin) return;
  if(url.pathname === "/logout") {
    event.respondWith((async()=>{
      await caches.delete(CACHE_NAME);
      return networkFirst(request);
    })());
    return;
  }
  if(isPrivate){
    event.respondWith(fetch(request).catch(async()=>{ const cached=await caches.match(request); return cached || (request.mode==="navigate" ? (await caches.match(OFFLINE_URL)) : Response.error()); }));
  } else {
    event.respondWith(networkFirst(request));
  }
});
