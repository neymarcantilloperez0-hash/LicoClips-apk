package com.licoclips.app;

import android.app.Activity;
import android.app.DownloadManager;
import android.content.ClipData;
import android.content.ClipboardManager;
import android.content.Context;
import android.content.Intent;
import android.net.Uri;
import android.os.Bundle;
import android.os.Environment;
import android.os.Handler;
import android.os.Looper;
import android.view.View;
import android.view.ViewGroup;
import android.webkit.CookieManager;
import android.webkit.JavascriptInterface;
import android.webkit.URLUtil;
import android.webkit.ValueCallback;
import android.webkit.WebChromeClient;
import android.webkit.WebResourceError;
import android.webkit.WebResourceRequest;
import android.webkit.WebSettings;
import android.webkit.WebView;
import android.webkit.WebViewClient;
import android.widget.FrameLayout;
import android.widget.Toast;

import java.net.HttpURLConnection;
import java.net.URL;

/**
 * LicoClips: envuelve el servidor local (Termux, puerto 5000) en una app.
 * Si el servidor esta apagado muestra una pantalla animada con los comandos para prenderlo
 * y abre la app sola en cuanto el servidor responde.
 */
public class MainActivity extends Activity {

    private static final String HOME = "http://127.0.0.1:5000/";
    private static final String PING = "http://127.0.0.1:5000/ping";
    private static final String OFFLINE = "file:///android_asset/offline.html";
    private static final int FILE_REQ = 4711;

    private WebView web;
    private FrameLayout root;
    private View customView;
    private WebChromeClient.CustomViewCallback customCb;
    private WebChromeClient chrome;
    private ValueCallback<Uri[]> fileCb;
    private boolean offline = false;
    private boolean polling = false;
    private final Handler handler = new Handler(Looper.getMainLooper());

    @Override
    protected void onCreate(Bundle savedInstanceState) {
        super.onCreate(savedInstanceState);
        root = new FrameLayout(this);
        root.setBackgroundColor(0xFF06121F);
        web = new WebView(this);
        web.setBackgroundColor(0xFF06121F);
        root.addView(web, new FrameLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.MATCH_PARENT));
        setContentView(root);

        WebSettings s = web.getSettings();
        s.setJavaScriptEnabled(true);
        s.setDomStorageEnabled(true);
        s.setMediaPlaybackRequiresUserGesture(false);
        s.setAllowFileAccess(true);
        s.setLoadWithOverviewMode(true);
        CookieManager.getInstance().setAcceptCookie(true);

        web.addJavascriptInterface(new Bridge(), "LicoBridge");

        web.setWebViewClient(new WebViewClient() {
            @Override
            public boolean shouldOverrideUrlLoading(WebView view, WebResourceRequest request) {
                Uri u = request.getUrl();
                String host = u.getHost() == null ? "" : u.getHost();
                String scheme = u.getScheme() == null ? "" : u.getScheme();
                if (scheme.equals("file") || host.equals("127.0.0.1") || host.equals("localhost")) {
                    return false;
                }
                try {
                    startActivity(new Intent(Intent.ACTION_VIEW, u));
                } catch (Exception e) {
                    Toast.makeText(MainActivity.this, "No pude abrir el enlace", Toast.LENGTH_SHORT).show();
                }
                return true;
            }

            @Override
            public void onReceivedError(WebView view, WebResourceRequest request, WebResourceError error) {
                if (request.isForMainFrame() && !offline) {
                    showOffline();
                }
            }

            @Override
            public void onPageFinished(WebView view, String url) {
                if (url != null && url.startsWith("http")) {
                    offline = false;
                }
            }
        });

        chrome = new WebChromeClient() {
            @Override
            public boolean onShowFileChooser(WebView webView, ValueCallback<Uri[]> callback, FileChooserParams params) {
                if (fileCb != null) {
                    fileCb.onReceiveValue(null);
                }
                fileCb = callback;
                try {
                    Intent i = new Intent(Intent.ACTION_GET_CONTENT);
                    i.addCategory(Intent.CATEGORY_OPENABLE);
                    i.setType("*/*");
                    String[] types = params.getAcceptTypes();
                    if (types != null && types.length > 0 && types[0] != null && !types[0].isEmpty()) {
                        i.putExtra(Intent.EXTRA_MIME_TYPES, types);
                        if (types.length == 1) {
                            i.setType(types[0]);
                        }
                    }
                    startActivityForResult(Intent.createChooser(i, "Elegir archivo"), FILE_REQ);
                } catch (Exception e) {
                    fileCb = null;
                    callback.onReceiveValue(null);
                    return false;
                }
                return true;
            }

            @Override
            public void onShowCustomView(View view, CustomViewCallback callback) {
                if (customView != null) {
                    callback.onCustomViewHidden();
                    return;
                }
                customView = view;
                customCb = callback;
                root.addView(view, new FrameLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.MATCH_PARENT));
                web.setVisibility(View.GONE);
            }

            @Override
            public void onHideCustomView() {
                if (customView == null) {
                    return;
                }
                root.removeView(customView);
                customView = null;
                web.setVisibility(View.VISIBLE);
                if (customCb != null) {
                    customCb.onCustomViewHidden();
                }
            }
        };
        web.setWebChromeClient(chrome);

        web.setDownloadListener((url, userAgent, contentDisposition, mimeType, contentLength) -> {
            try {
                String name = URLUtil.guessFileName(url, contentDisposition, mimeType);
                DownloadManager.Request r = new DownloadManager.Request(Uri.parse(url));
                r.setMimeType(mimeType);
                r.setTitle(name);
                r.setNotificationVisibility(DownloadManager.Request.VISIBILITY_VISIBLE_NOTIFY_COMPLETED);
                r.setDestinationInExternalPublicDir(Environment.DIRECTORY_DOWNLOADS, name);
                DownloadManager dm = (DownloadManager) getSystemService(Context.DOWNLOAD_SERVICE);
                dm.enqueue(r);
                Toast.makeText(MainActivity.this, "Descargando en Descargas: " + name, Toast.LENGTH_LONG).show();
            } catch (Exception e) {
                Toast.makeText(MainActivity.this, "No pude descargar: " + e.getMessage(), Toast.LENGTH_LONG).show();
            }
        });

        tryStart();
    }

    /** Revisa si el servidor responde; si si abre la app, si no muestra la pantalla de apagado. */
    private void tryStart() {
        new Thread(() -> {
            final boolean up = serverUp();
            runOnUiThread(() -> {
                if (up) {
                    offline = false;
                    web.loadUrl(HOME);
                } else {
                    showOffline();
                }
            });
        }).start();
    }

    private boolean serverUp() {
        HttpURLConnection c = null;
        try {
            c = (HttpURLConnection) new URL(PING).openConnection();
            c.setConnectTimeout(1500);
            c.setReadTimeout(1500);
            c.setUseCaches(false);
            return c.getResponseCode() == 200;
        } catch (Exception e) {
            return false;
        } finally {
            if (c != null) {
                c.disconnect();
            }
        }
    }

    private void showOffline() {
        offline = true;
        web.loadUrl(OFFLINE);
        startPolling();
    }

    private void startPolling() {
        if (polling) {
            return;
        }
        polling = true;
        handler.postDelayed(pollTask, 3000);
    }

    private final Runnable pollTask = new Runnable() {
        @Override
        public void run() {
            if (!offline) {
                polling = false;
                return;
            }
            new Thread(() -> {
                final boolean up = serverUp();
                runOnUiThread(() -> {
                    if (up && offline) {
                        offline = false;
                        polling = false;
                        web.loadUrl(HOME);
                    } else if (offline) {
                        handler.postDelayed(pollTask, 3000);
                    } else {
                        polling = false;
                    }
                });
            }).start();
        }
    };

    /** Funciones que usa la pantalla "servidor apagado". */
    private class Bridge {
        @JavascriptInterface
        public void retry() {
            runOnUiThread(() -> tryStart());
        }

        @JavascriptInterface
        public void copy(String text) {
            runOnUiThread(() -> {
                ClipboardManager cm = (ClipboardManager) getSystemService(Context.CLIPBOARD_SERVICE);
                cm.setPrimaryClip(ClipData.newPlainText("comandos", text));
                Toast.makeText(MainActivity.this, "Comandos copiados", Toast.LENGTH_SHORT).show();
            });
        }
    }

    @Override
    protected void onActivityResult(int requestCode, int resultCode, Intent data) {
        if (requestCode == FILE_REQ) {
            if (fileCb != null) {
                Uri[] result = null;
                if (resultCode == RESULT_OK && data != null) {
                    if (data.getClipData() != null) {
                        int n = data.getClipData().getItemCount();
                        result = new Uri[n];
                        for (int i = 0; i < n; i++) {
                            result[i] = data.getClipData().getItemAt(i).getUri();
                        }
                    } else if (data.getData() != null) {
                        result = new Uri[]{data.getData()};
                    }
                }
                fileCb.onReceiveValue(result);
                fileCb = null;
            }
            return;
        }
        super.onActivityResult(requestCode, resultCode, data);
    }

    @Override
    public void onBackPressed() {
        if (customView != null) {
            chrome.onHideCustomView();
        } else if (!offline && web.canGoBack()) {
            web.goBack();
        } else {
            super.onBackPressed();
        }
    }

    @Override
    protected void onResume() {
        super.onResume();
        web.onResume();
        if (offline) {
            startPolling();
        }
    }

    @Override
    protected void onPause() {
        web.onPause();
        super.onPause();
    }

    @Override
    protected void onDestroy() {
        handler.removeCallbacksAndMessages(null);
        web.destroy();
        super.onDestroy();
    }
}
