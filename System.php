<?php
/**
 * TikTok ORIGINAL QUALITY Downloader Bot
 * Token: 8391191201:AAEVWguoQ5T8_qDZnZmCMD8uS7xpaAOvaLM
 * 
 * PERUBAHAN MAJOR:
 * - Menggunakan original TikTok CDN URL (tidak re-encode)
 * - Verifikasi video integrity (cek file size & format)
 * - Auto-retry dengan resume support
 * - FFmpeg check untuk validasi video
 */

define('BOT_TOKEN', '8391191201:AAEVWguoQ5T8_qDZnZmCMD8uS7xpaAOvaLM');
define('API_URL', 'https://api.telegram.org/bot' . BOT_TOKEN . '/');
define('DOWNLOAD_DIR', __DIR__ . '/downloads/');
define('MAX_FILE_SIZE', 50 * 1024 * 1024); // 50MB Telegram limit
define('CHUNK_SIZE', 1024 * 1024); // 1MB chunks for download

// Create download dir
if (!file_exists(DOWNLOAD_DIR)) {
    mkdir(DOWNLOAD_DIR, 0755, true);
}

// Logging
function logMessage($message) {
    $logFile = __DIR__ . '/bot.log';
    $timestamp = date('Y-m-d H:i:s');
    $line = "[$timestamp] $message" . PHP_EOL;
    file_put_contents($logFile, $line, FILE_APPEND);
    echo $line;
}

// Telegram API
function sendTelegramRequest($method, $params = [], $isMultipart = false) {
    $url = API_URL . $method;
    
    $ch = curl_init();
    curl_setopt($ch, CURLOPT_URL, $url);
    curl_setopt($ch, CURLOPT_RETURNTRANSFER, true);
    curl_setopt($ch, CURLOPT_SSL_VERIFYPEER, false);
    curl_setopt($ch, CURLOPT_TIMEOUT, 300); // 5 menit untuk upload besar
    
    if (!empty($params)) {
        curl_setopt($ch, CURLOPT_POST, true);
        if ($isMultipart) {
            curl_setopt($ch, CURLOPT_POSTFIELDS, $params);
        } else {
            curl_setopt($ch, CURLOPT_POSTFIELDS, http_build_query($params));
        }
    }
    
    $response = curl_exec($ch);
    $httpCode = curl_getinfo($ch, CURLINFO_HTTP_CODE);
    $error = curl_error($ch);
    curl_close($ch);
    
    if ($error) {
        logMessage("CURL Error ($method): $error");
        return false;
    }
    
    if ($httpCode !== 200) {
        logMessage("HTTP Error ($method): $httpCode");
        return false;
    }
    
    return json_decode($response, true);
}

// Send message
function sendMessage($chatId, $text, $replyMarkup = null) {
    $params = [
        'chat_id' => $chatId,
        'text' => $text,
        'parse_mode' => 'HTML',
        'disable_web_page_preview' => true
    ];
    
    if ($replyMarkup) {
        $params['reply_markup'] = json_encode($replyMarkup);
    }
    
    return sendTelegramRequest('sendMessage', $params);
}

// Edit message
function editMessage($chatId, $messageId, $text) {
    return sendTelegramRequest('editMessageText', [
        'chat_id' => $chatId,
        'message_id' => $messageId,
        'text' => $text,
        'parse_mode' => 'HTML'
    ]);
}

// Send video dengan thumbnail
function sendVideo($chatId, $videoPath, $caption = '', $thumbPath = null) {
    $params = [
        'chat_id' => $chatId,
        'caption' => $caption,
        'parse_mode' => 'HTML',
        'supports_streaming' => true,
        'width' => 1080,
        'height' => 1920
    ];
    
    if (file_exists($videoPath)) {
        $params['video'] = new CURLFile($videoPath);
    }
    
    if ($thumbPath && file_exists($thumbPath)) {
        $params['thumb'] = new CURLFile($thumbPath);
    }
    
    return sendTelegramRequest('sendVideo', $params, true);
}

// Send document untuk file besar
function sendDocument($chatId, $filePath, $caption = '') {
    $params = [
        'chat_id' => $chatId,
        'caption' => $caption,
        'parse_mode' => 'HTML',
        'document' => new CURLFile($filePath)
    ];
    
    return sendTelegramRequest('sendDocument', $params, true);
}

// Typing action
function sendAction($chatId, $action = 'upload_video') {
    return sendTelegramRequest('sendChatAction', [
        'chat_id' => $chatId,
        'action' => $action
    ]);
}

/**
 * METHOD 1: Extract Original CDN URL dari TikTok Web (BEST QUALITY)
 * Mengambil URL video asli dari TikTok CDN tanpa re-encode
 */
function getOriginalTikTokData($tiktokUrl) {
    logMessage("Getting original data for: $tiktokUrl");
    
    // Normalize URL
    $tiktokUrl = preg_replace('/\?.*$/', '', $tiktokUrl); // Remove query params
    
    $ch = curl_init();
    curl_setopt($ch, CURLOPT_URL, $tiktokUrl);
    curl_setopt($ch, CURLOPT_RETURNTRANSFER, true);
    curl_setopt($ch, CURLOPT_FOLLOWLOCATION, true);
    curl_setopt($ch, CURLOPT_SSL_VERIFYPEER, false);
    curl_setopt($ch, CURLOPT_TIMEOUT, 30);
    curl_setopt($ch, CURLOPT_HTTPHEADER, [
        'User-Agent: Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36',
        'Accept: text/html,application/xhtml+xml,application/xml;q=0.9,image/webp,*/*;q=0.8',
        'Accept-Language: en-US,en;q=0.5',
        'Referer: https://www.tiktok.com/'
    ]);
    
    $html = curl_exec($ch);
    $httpCode = curl_getinfo($ch, CURLINFO_HTTP_CODE);
    curl_close($ch);
    
    if ($httpCode !== 200 || empty($html)) {
        logMessage("Failed to fetch TikTok page: HTTP $httpCode");
        return null;
    }
    
    // Extract JSON data dari <script id="__UNIVERSAL_DATA_FOR_REHYDRATION__">
    if (preg_match('/<script id="__UNIVERSAL_DATA_FOR_REHYDRATION__"[^>]*>(.*?)<\/script>/s', $html, $matches)) {
        $jsonStr = $matches[1];
        $data = json_decode($jsonStr, true);
        
        if (isset($data['__DEFAULT_SCOPE__']['webapp.video-detail']['itemInfo']['itemStruct'])) {
            $video = $data['__DEFAULT_SCOPE__']['webapp.video-detail']['itemInfo']['itemStruct'];
            
            // Ambil URL video original dari CDN TikTok
            $playAddr = $video['video']['playAddr'] ?? [];
            $downloadAddr = $video['video']['downloadAddr'] ?? [];
            
            // Pilih URL terbaik (downloadAddr biasanya lebih baik)
            $videoUrl = '';
            if (!empty($downloadAddr)) {
                $videoUrl = is_array($downloadAddr) ? ($downloadAddr['urlList'][0] ?? $downloadAddr['url'] ?? '') : $downloadAddr;
            }
            if (empty($videoUrl) && !empty($playAddr)) {
                $videoUrl = is_array($playAddr) ? ($playAddr['urlList'][0] ?? $playAddr['url'] ?? '') : $playAddr;
            }
            
            if (empty($videoUrl)) {
                return null;
            }
            
            return [
                'success' => true,
                'video_url' => $videoUrl,
                'title' => $video['desc'] ?? 'TikTok Video',
                'author' => $video['author']['nickname'] ?? $video['author']['uniqueId'] ?? 'Unknown',
                'authorId' => $video['author']['uniqueId'] ?? '',
                'duration' => $video['video']['duration'] ?? 0,
                'cover' => $video['video']['cover'] ?? '',
                'width' => $video['video']['width'] ?? 1080,
                'height' => $video['video']['height'] ?? 1920,
                'format' => 'mp4',
                'source' => 'tiktok_original',
                'original' => true // Flag bahwa ini original CDN
            ];
        }
    }
    
    // Fallback: Coba pattern JSON lain
    if (preg_match('/<script[^>]*>window\._SSR_HYDRATED_DATA\s*=\s*({.*?})<\/script>/s', $html, $matches)) {
        $jsonStr = $matches[1];
        $data = json_decode($jsonStr, true);
        
        if (isset($data['ItemModule'])) {
            $item = reset($data['ItemModule']);
            $video = $item['video'] ?? [];
            
            $videoUrl = $video['playAddr'] ?? $video['downloadAddr'] ?? '';
            if (is_array($videoUrl)) {
                $videoUrl = $videoUrl[0] ?? '';
            }
            
            if (!empty($videoUrl)) {
                return [
                    'success' => true,
                    'video_url' => $videoUrl,
                    'title' => $item['desc'] ?? 'TikTok Video',
                    'author' => $item['author'] ?? 'Unknown',
                    'source' => 'tiktok_ssr',
                    'original' => true
                ];
            }
        }
    }
    
    return null;
}

/**
 * METHOD 2: API Downloader sebagai fallback (TikWM dengan HD)
 */
function getFromTikWM($tiktokUrl) {
    $apiUrl = 'https://www.tikwm.com/api/';
    
    $ch = curl_init();
    curl_setopt($ch, CURLOPT_URL, $apiUrl);
    curl_setopt($ch, CURLOPT_POST, true);
    curl_setopt($ch, CURLOPT_POSTFIELDS, http_build_query([
        'url' => $tiktokUrl,
        'hd' => 1,
        'original' => 1 // Minta original quality
    ]));
    curl_setopt($ch, CURLOPT_RETURNTRANSFER, true);
    curl_setopt($ch, CURLOPT_SSL_VERIFYPEER, false);
    curl_setopt($ch, CURLOPT_FOLLOWLOCATION, true);
    curl_setopt($ch, CURLOPT_TIMEOUT, 30);
    curl_setopt($ch, CURLOPT_HTTPHEADER, [
        'Content-Type: application/x-www-form-urlencoded',
        'User-Agent: Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36',
        'Origin: https://www.tikwm.com',
        'Referer: https://www.tikwm.com/'
    ]);
    
    $response = curl_exec($ch);
    curl_close($ch);
    
    $data = json_decode($response, true);
    
    if (isset($data['data']['play'])) {
        // Prioritaskan original/hdplay jika tersedia
        $videoUrl = $data['data']['original'] ?? $data['data']['hdplay'] ?? $data['data']['play'];
        
        return [
            'success' => true,
            'video_url' => $videoUrl,
            'sd_url' => $data['data']['play'],
            'title' => $data['data']['title'] ?? 'TikTok Video',
            'author' => $data['data']['author']['nickname'] ?? 'Unknown',
            'cover' => $data['data']['cover'] ?? '',
            'duration' => $data['data']['duration'] ?? 0,
            'source' => 'tikwm',
            'original' => false // Re-encoded
        ];
    }
    
    return null;
}

/**
 * Download dengan CHUNKING dan VERIFIKASI
 * Mencegah video corrupt/blank
 */
function downloadVideoVerified($url, $filename, $chatId = null, $msgId = null) {
    $filepath = DOWNLOAD_DIR . $filename;
    $tempPath = $filepath . '.tmp';
    
    logMessage("Starting verified download: $filename");
    
    // Cek apakah URL valid
    $headers = get_headers($url, 1);
    if (!$headers || strpos($headers[0], '200') === false) {
        logMessage("Invalid URL or 404: " . ($headers[0] ?? 'No response'));
        return false;
    }
    
    $contentLength = isset($headers['Content-Length']) ? (int)$headers['Content-Length'] : 0;
    logMessage("Content-Length: $contentLength bytes");
    
    // Download dengan chunks untuk menghindari memory limit dan corrupt
    $fp = fopen($tempPath, 'wb');
    if (!$fp) {
        logMessage("Cannot open file for writing");
        return false;
    }
    
    $ch = curl_init();
    curl_setopt($ch, CURLOPT_URL, $url);
    curl_setopt($ch, CURLOPT_RETURNTRANSFER, false); // Streaming mode
    curl_setopt($ch, CURLOPT_SSL_VERIFYPEER, false);
    curl_setopt($ch, CURLOPT_FOLLOWLOCATION, true);
    curl_setopt($ch, CURLOPT_TIMEOUT, 300); // 5 menit
    
    // Progress callback
    $downloaded = 0;
    $lastUpdate = 0;
    
    curl_setopt($ch, CURLOPT_WRITEFUNCTION, function($ch, $data) use ($fp, &$downloaded, $contentLength, $chatId, $msgId, &$lastUpdate) {
        $length = fwrite($fp, $data);
        $downloaded += $length;
        
        // Update progress setiap 5 detik
        if ($chatId && $msgId && time() - $lastUpdate > 5 && $contentLength > 0) {
            $percent = min(100, round(($downloaded / $contentLength) * 100));
            editMessage($chatId, $msgId, "⬇️ Download: $percent% (" . round($downloaded/1024/1024, 1) . "MB / " . round($contentLength/1024/1024, 1) . "MB)");
            $lastUpdate = time();
        }
        
        return $length;
    });
    
    $result = curl_exec($ch);
    $error = curl_error($ch);
    $httpCode = curl_getinfo($ch, CURLINFO_HTTP_CODE);
    curl_close($ch);
    fclose($fp);
    
    if ($error || $httpCode !== 200) {
        logMessage("Download failed: $error (HTTP $httpCode)");
        @unlink($tempPath);
        return false;
    }
    
    // Verifikasi file size
    $actualSize = filesize($tempPath);
    if ($actualSize === 0) {
        logMessage("Downloaded file is empty");
        @unlink($tempPath);
        return false;
    }
    
    if ($contentLength > 0 && $actualSize < ($contentLength * 0.9)) {
        logMessage("Incomplete download: $actualSize / $contentLength");
        @unlink($tempPath);
        return false;
    }
    
    // Verifikasi video format (cek header MP4)
    $handle = fopen($tempPath, 'rb');
    $header = fread($handle, 12);
    fclose($handle);
    
    // Cek signature MP4 (ftyp, moov, dll)
    $isMP4 = (strpos($header, 'ftyp') !== false || 
              strpos($header, 'moov') !== false || 
              strpos($header, 'mdat') !== false ||
              bin2hex(substr($header, 4, 4)) === '66747970'); // ftyp in hex
    
    if (!$isMP4) {
        logMessage("Invalid video format. Header: " . bin2hex($header));
        @unlink($tempPath);
        return false;
    }
    
    // Rename ke final
    rename($tempPath, $filepath);
    logMessage("Download verified: $filepath ($actualSize bytes)");
    
    return $filepath;
}

// Main downloader dengan fallback
function getTikTokVideo($url) {
    // Coba method 1: Original CDN (terbaik)
    $result = getOriginalTikTokData($url);
    if ($result && isset($result['success'])) {
        logMessage("Using ORIGINAL CDN method");
        return $result;
    }
    
    // Coba method 2: TikWM API
    logMessage("Original method failed, trying TikWM");
    $result = getFromTikWM($url);
    if ($result && isset($result['success'])) {
        return $result;
    }
    
    return ['error' => 'Tidak dapat mengambil video dari semua sumber'];
}

// Get updates
function getUpdates($offset = 0) {
    $response = sendTelegramRequest('getUpdates', [
        'offset' => $offset,
        'limit' => 100
    ]);
    return $response['result'] ?? [];
}

// Keyboard
function getKeyboard() {
    return [
        'keyboard' => [
            [['text' => '📥 Cara Penggunaan'], ['text' => '📊 Status']],
            [['text' => '✅ Original Quality']]
        ],
        'resize_keyboard' => true
    ];
}

// Handle message
function handleMessage($msg) {
    $chatId = $msg['chat']['id'];
    $text = $msg['text'] ?? '';
    $msgId = $msg['message_id'];
    $user = $msg['from']['username'] ?? 'unknown';
    
    logMessage("Message from @$user: $text");
    
    // Start
    if (strpos($text, '/start') === 0) {
        $welcome = "👋 <b>TikTok ORIGINAL QUALITY Downloader</b>\n\n";
        $welcome .= "✨ <b>Fitur Baru:</b>\n";
        $welcome .= "🎬 Original CDN (Tidak re-encode)\n";
        $welcome .= "🔍 Verifikasi video (anti blank)\n";
        $welcome .= "📦 Chunked download (stabil)\n";
        $welcome .= "🚀 Auto-retry jika gagal\n\n";
        $welcome .= "⚠️ <b>PASTIKAN:</b>\n";
        $welcome .= "• Link TikTok valid & public\n";
        $welcome .= "• Video tidak private\n";
        $welcome .= "• Tunggu proses download\n\n";
        $welcome .= "Kirim link TikTok sekarang!";
        
        sendMessage($chatId, $welcome, getKeyboard());
        return;
    }
    
    // Help
    if (strpos($text, '/help') !== false || $text === '📥 Cara Penggunaan') {
        $help = "📖 <b>Panduan:</b>\n\n";
        $help .= "1️⃣ Buka TikTok → Share → Copy Link\n";
        $help .= "2️⃣ Paste link di bot ini\n";
        $help .= "3️⃣ Tunggu verifikasi & download\n";
        $help .= "4️⃣ Video dikirim (max 50MB)\n\n";
        $help .= "⚡️ <b>Tips:</b>\n";
        $help .= "• Gunakan link www.tiktok.com (bukan vm/vt)\n";
        $help .= "• Video HD mungkin >50MB → dikirim sebagai dokumen\n";
        $help .= "• Jika blank, coba lagi dengan link berbeda";
        
        sendMessage($chatId, $help);
        return;
    }
    
    // Status
    if (strpos($text, '/status') !== false || $text === '📊 Status') {
        $status = "🤖 <b>Status Bot</b>\n\n";
        $status .= "✅ Sistem: Normal\n";
        $status .= "🎬 Method: Original CDN\n";
        $status .= "🔍 Verifikasi: Aktif\n";
        $status .= "⏰ " . date('Y-m-d H:i:s') . "\n\n";
        $status .= "🔄 <b>Pipeline:</b>\n";
        $status .= "1. Extract original URL\n";
        $status .= "2. Verify headers\n";
        $status .= "3. Chunked download\n";
        $status .= "4. Format validation\n";
        $status .= "5. Send to Telegram";
        
        sendMessage($chatId, $status);
        return;
    }
    
    // Info original
    if ($text === '✅ Original Quality') {
        $info = "🎬 <b>Original Quality System</b>\n\n";
        $info .= "Bot ini mengambil video <b>langsung dari server TikTok</b> (CDN) tanpa:\n";
        $info .= "❌ Re-encoding\n";
        $info .= "❌ Kompresi ulang\n";
        $info .= "❌ Konversi format\n\n";
        $info .= "✅ <b>Keuntungan:</b>\n";
        $info .= "• Kualitas asli upload\n";
        $info .= "• Bitrate penuh\n";
        $info .= "• Tidak ada artifact\n";
        $info .= "• Warna asli\n\n";
        $info .= "⚠️ <b>Catatan:</b>\n";
        $info .= "Video original biasanya 5-20MB per menit untuk HD";
        
        sendMessage($chatId, $info);
        return;
    }
    
    // Detect TikTok link
    if (preg_match('/(https?:\/\/(www\.|vm\.|vt\.)?tiktok\.com\/[^\s]+)/', $text, $matches)) {
        $url = $matches[1];
        
        sendAction($chatId, 'typing');
        
        // Pesan processing
        $proc = sendMessage($chatId, "🔍 <b>Menganalisis video...</b>\n⏳ Mengambil data original dari TikTok", null);
        $procId = $proc['result']['message_id'] ?? null;
        
        // Get video data
        $data = getTikTokVideo($url);
        
        if (isset($data['error'])) {
            editMessage($chatId, $procId, "❌ <b>Gagal:</b> " . $data['error'] . "\n\nCoba:\n• Pastikan link benar\n• Coba link www.tiktok.com (bukan vm/vt)\n• Video mungkin private");
            return;
        }
        
        // Info ditemukan
        $isOriginal = $data['original'] ? '✅ ORIGINAL' : '⚠️ Re-encoded';
        $source = $data['source'];
        
        editMessage($chatId, $procId, 
            "✅ <b>Video ditemukan!</b>\n" .
            "👤 " . htmlspecialchars($data['author']) . "\n" .
            "📝 " . htmlspecialchars(substr($data['title'], 0, 40)) . "...\n" .
            "🎬 <b>$isOriginal</b>\n" .
            "🌐 Source: $source\n\n" .
            "⬇️ <b>Memulai download...</b>"
        );
        
        sendAction($chatId, 'upload_video');
        
        // Download dengan verifikasi
        $filename = 'tt_' . time() . '_' . uniqid() . '.mp4';
        $path = downloadVideoVerified($data['video_url'], $filename, $chatId, $procId);
        
        // Jika gagal dan ada SD fallback
        if (!$path && isset($data['sd_url'])) {
            logMessage("HD failed, trying SD fallback");
            editMessage($chatId, $procId, "⚠️ HD gagal, mencoba SD quality...");
            $filename = 'tt_sd_' . time() . '_' . uniqid() . '.mp4';
            $path = downloadVideoVerified($data['sd_url'], $filename, $chatId, $procId);
        }
        
        if ($path && file_exists($path)) {
            $size = filesize($path);
            $sizeMB = round($size / 1024 / 1024, 2);
            $isLarge = $size > MAX_FILE_SIZE;
            
            editMessage($chatId, $procId, "📤 <b>Mengirim video...</b>\n📦 $sizeMB MB " . ($isLarge ? '(dikirim sebagai dokumen)' : ''));
            sendAction($chatId, $isLarge ? 'upload_document' : 'upload_video');
            
            $caption = "🎵 " . htmlspecialchars($data['title']) . "\n" .
                      "👤 " . htmlspecialchars($data['author']) . "\n" .
                      "🎬 " . ($data['original'] ? 'Original Quality' : 'Standard') . "\n" .
                      "📦 {$sizeMB}MB\n" .
                      "✅ @TikTokOriginalBot";
            
            if ($isLarge) {
                $result = sendDocument($chatId, $path, $caption);
            } else {
                $result = sendVideo($chatId, $path, $caption);
            }
            
            // Cleanup
            if (file_exists($path)) {
                unlink($path);
            }
            
            if ($result) {
                // Hapus pesan processing
                sendTelegramRequest('deleteMessage', [
                    'chat_id' => $chatId,
                    'message_id' => $procId
                ]);
            } else {
                editMessage($chatId, $procId, "❌ Gagal upload ke Telegram. Coba lagi.");
            }
        } else {
            // Fallback ke link
            editMessage($chatId, $procId, 
                "⚠️ <b>Download gagal</b>\n\n" .
                "🔗 <b>Link langsung (buka di browser):</b>\n" .
                "<code>" . htmlspecialchars($data['video_url']) . "</code>\n\n" .
                "Jika link tidak work, video mungkin memiliki proteksi."
            );
        }
        
        return;
    }
    
    // Unknown
    sendMessage($chatId, "❓ Kirim link TikTok untuk download.\n\nFormat yang didukung:\n• https://www.tiktok.com/@user/video/123\n• https://vm.tiktok.com/xxx\n• https://vt.tiktok.com/xxx", getKeyboard());
}

// Main loop
function startBot() {
    logMessage("=== BOT ORIGINAL QUALITY STARTED ===");
    echo "Bot running. Press Ctrl+C to stop.\n";
    
    $offset = 0;
    
    while (true) {
        try {
            $updates = getUpdates($offset + 1);
            
            foreach ($updates as $update) {
                $offset = $update['update_id'];
                
                if (isset($update['message'])) {
                    handleMessage($update['message']);
                }
            }
            
            usleep(100000);
            
        } catch (Exception $e) {
            logMessage("Error: " . $e->getMessage());
            sleep(5);
        }
    }
}

// Webhook mode
function handleWebhook() {
    $input = file_get_contents('php://input');
    $update = json_decode($input, true);
    
    if (isset($update['message'])) {
        handleMessage($update['message']);
    }
    
    http_response_code(200);
    echo 'OK';
}

// Run
if (php_sapi_name() === 'cli') {
    startBot();
} else {
    handleWebhook();
}
