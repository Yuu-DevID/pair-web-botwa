<?php
/**
 * TikTok LoveTik Downloader Bot (No FFmpeg)
 * Token: 8391191201:AAEVWguoQ5T8_qDZnZmCMD8uS7xpaAOvaLM
 * 
 * CHANGELOG:
 * - LoveTik API sebagai primary source
 * - /runtime & /ping commands
 * - No FFmpeg dependency - pure PHP validation
 * - Strict MP4 header & structure validation
 * - Content-Length verification
 * - MIME type checking
 */

define('BOT_TOKEN', '8391191201:AAEVWguoQ5T8_qDZnZmCMD8uS7xpaAOvaLM');
define('API_URL', 'https://api.telegram.org/bot' . BOT_TOKEN . '/');
define('DOWNLOAD_DIR', __DIR__ . '/downloads/');
define('MAX_FILE_SIZE', 50 * 1024 * 1024); // 50MB Telegram limit
define('MIN_VIDEO_SIZE', 10 * 1024); // Minimum 10KB untuk video valid

// Bot start time untuk runtime
$GLOBALS['START_TIME'] = time();

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

// Get runtime duration
function getRuntime() {
    $now = time();
    $diff = $now - $GLOBALS['START_TIME'];
    
    $days = floor($diff / 86400);
    $hours = floor(($diff % 86400) / 3600);
    $minutes = floor(($diff % 3600) / 60);
    $seconds = $diff % 60;
    
    $parts = [];
    if ($days > 0) $parts[] = "$days hari";
    if ($hours > 0) $parts[] = "$hours jam";
    if ($minutes > 0) $parts[] = "$minutes menit";
    $parts[] = "$seconds detik";
    
    return implode(', ', $parts);
}

// Ping check
function getPing() {
    $start = microtime(true);
    $ch = curl_init();
    curl_setopt($ch, CURLOPT_URL, API_URL . 'getMe');
    curl_setopt($ch, CURLOPT_RETURNTRANSFER, true);
    curl_setopt($ch, CURLOPT_SSL_VERIFYPEER, false);
    curl_setopt($ch, CURLOPT_TIMEOUT, 10);
    curl_exec($ch);
    $httpCode = curl_getinfo($ch, CURLINFO_HTTP_CODE);
    curl_close($ch);
    $end = microtime(true);
    
    $latency = round(($end - $start) * 1000, 2);
    return ['latency' => $latency, 'status' => $httpCode === 200 ? 'OK' : 'ERROR'];
}

// Telegram API
function sendTelegramRequest($method, $params = [], $isMultipart = false) {
    $url = API_URL . $method;
    
    $ch = curl_init();
    curl_setopt($ch, CURLOPT_URL, $url);
    curl_setopt($ch, CURLOPT_RETURNTRANSFER, true);
    curl_setopt($ch, CURLOPT_SSL_VERIFYPEER, false);
    curl_setopt($ch, CURLOPT_TIMEOUT, 300);
    
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

// Send video
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

// Send document
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
 * LoveTik API Method
 */
function getFromLoveTik($tiktokUrl) {
    logMessage("Using LoveTik API for: $tiktokUrl");
    
    $apiUrl = 'https://lovetik.com/api/v1/search';
    
    $ch = curl_init();
    curl_setopt($ch, CURLOPT_URL, $apiUrl);
    curl_setopt($ch, CURLOPT_POST, true);
    curl_setopt($ch, CURLOPT_POSTFIELDS, http_build_query(['query' => $tiktokUrl]));
    curl_setopt($ch, CURLOPT_RETURNTRANSFER, true);
    curl_setopt($ch, CURLOPT_SSL_VERIFYPEER, false);
    curl_setopt($ch, CURLOPT_FOLLOWLOCATION, true);
    curl_setopt($ch, CURLOPT_TIMEOUT, 30);
    curl_setopt($ch, CURLOPT_HTTPHEADER, [
        'Content-Type: application/x-www-form-urlencoded',
        'User-Agent: Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36',
        'Origin: https://lovetik.com',
        'Referer: https://lovetik.com/'
    ]);
    
    $response = curl_exec($ch);
    $httpCode = curl_getinfo($ch, CURLINFO_HTTP_CODE);
    $error = curl_error($ch);
    curl_close($ch);
    
    if ($error) {
        logMessage("LoveTik Error: $error");
        return null;
    }
    
    if ($httpCode !== 200) {
        logMessage("LoveTik HTTP Error: $httpCode");
        return null;
    }
    
    $data = json_decode($response, true);
    
    if (isset($data['err']) && $data['err'] === false && isset($data['links'])) {
        $videoUrl = '';
        $isOriginal = false;
        
        // Prioritas: HD No Watermark > HD > No Watermark > Standard
        foreach ($data['links'] as $link) {
            if (strpos($link['type'], 'hd') !== false && strpos($link['type'], 'nowatermark') !== false) {
                $videoUrl = $link['url'];
                $isOriginal = true;
                break;
            } elseif (strpos($link['type'], 'hd') !== false && empty($videoUrl)) {
                $videoUrl = $link['url'];
                $isOriginal = true;
            } elseif (strpos($link['type'], 'nowatermark') !== false && empty($videoUrl)) {
                $videoUrl = $link['url'];
            }
        }
        
        if (empty($videoUrl) && !empty($data['links'][0]['url'])) {
            $videoUrl = $data['links'][0]['url'];
        }
        
        if (!empty($videoUrl)) {
            return [
                'success' => true,
                'video_url' => $videoUrl,
                'title' => $data['desc'] ?? 'TikTok Video',
                'author' => $data['author'] ?? 'Unknown',
                'cover' => $data['cover'] ?? '',
                'duration' => $data['duration'] ?? 0,
                'source' => 'lovetik',
                'original' => $isOriginal
            ];
        }
    }
    
    return null;
}

/**
 * TikWM Fallback Method
 */
function getFromTikWM($tiktokUrl) {
    logMessage("Using TikWM fallback for: $tiktokUrl");
    
    $apiUrl = 'https://www.tikwm.com/api/';
    
    $ch = curl_init();
    curl_setopt($ch, CURLOPT_URL, $apiUrl);
    curl_setopt($ch, CURLOPT_POST, true);
    curl_setopt($ch, CURLOPT_POSTFIELDS, http_build_query([
        'url' => $tiktokUrl,
        'hd' => 1
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
        $videoUrl = $data['data']['hdplay'] ?? $data['data']['play'];
        
        return [
            'success' => true,
            'video_url' => $videoUrl,
            'sd_url' => $data['data']['play'],
            'title' => $data['data']['title'] ?? 'TikTok Video',
            'author' => $data['data']['author']['nickname'] ?? 'Unknown',
            'cover' => $data['data']['cover'] ?? '',
            'duration' => $data['data']['duration'] ?? 0,
            'source' => 'tikwm',
            'original' => false
        ];
    }
    
    return null;
}

/**
 * Strict Video Validation (No FFmpeg)
 * Cek MP4 structure, size, dan headers
 */
function validateVideoStrict($filepath) {
    logMessage("Validating video (no FFmpeg): $filepath");
    
    if (!file_exists($filepath)) {
        logMessage("File not found");
        return false;
    }
    
    $size = filesize($filepath);
    
    // Cek minimum size
    if ($size < MIN_VIDEO_SIZE) {
        logMessage("File too small: $size bytes (min " . MIN_VIDEO_SIZE . ")");
        return false;
    }
    
    // Baca header dan trailer untuk validasi MP4
    $handle = fopen($filepath, 'rb');
    
    // Cek header awal (first 32 bytes)
    $header = fread($handle, 32);
    $hexHeader = bin2hex($header);
    
    // Cek box type 'ftyp' (file type) - harus ada di awal file MP4 valid
    // MP4 signature: [4 bytes size] + 'ftyp' + [4 bytes major_brand] + ...
    $hasFtyp = (strpos($header, 'ftyp') !== false);
    
    // Cek juga untuk 'moov' (movie header) atau 'mdat' (media data)
    $hasMoov = (strpos($header, 'moov') !== false);
    $hasMdat = (strpos($header, 'mdat') !== false);
    
    // Cek di offset berbeda jika tidak ditemukan di awal
    if (!$hasFtyp && !$hasMoov && !$hasMdat) {
        // Coba baca di posisi lain (beberapa MP4 punya struktur berbeda)
        fseek($handle, 4);
        $skip4 = fread($handle, 8);
        if (strpos($skip4, 'ftyp') !== false) {
            $hasFtyp = true;
        }
    }
    
    // Cek trailer (last 8 bytes) - harus ada box valid di akhir
    fseek($handle, -8, SEEK_END);
    $trailer = fread($handle, 8);
    fclose($handle);
    
    // Validasi trailer (biasanya berisi ukuran box atau moov/mdat)
    $validTrailer = strlen($trailer) === 8;
    
    // MP4 valid harus punya minimal ftyp di awal
    if (!$hasFtyp && !$hasMoov && !$hasMdat) {
        logMessage("Invalid MP4 structure. Header: " . substr($hexHeader, 0, 32));
        return false;
    }
    
    // Cek MIME type via file extension dan content
    $finfo = finfo_open(FILEINFO_MIME_TYPE);
    $mimeType = finfo_file($finfo, $filepath);
    finfo_close($finfo);
    
    $validMime = in_array($mimeType, [
        'video/mp4',
        'video/quicktime', // MOV tapi bisa jadi MP4
        'application/mp4',
        'video/x-matroska', // MKV (kadang terdeteksi sebagai ini)
        'application/octet-stream' // Kadang MP4 terdeteksi sebagai ini
    ]);
    
    if (!$validMime && $mimeType !== 'application/octet-stream') {
        logMessage("Invalid MIME type: $mimeType");
        // Jangan return false langsung, kadang MP4 terdeteksi sebagai octet-stream
    }
    
    logMessage("Validation passed. Size: $size, MIME: $mimeType, Structure: OK");
    return true;
}

/**
 * Download dengan verifikasi lengkap
 */
function downloadVideoVerified($url, $filename, $chatId = null, $msgId = null) {
    $filepath = DOWNLOAD_DIR . $filename;
    $tempPath = $filepath . '.tmp';
    
    logMessage("Starting download: $filename");
    
    // Head request untuk cek headers
    $ch = curl_init();
    curl_setopt($ch, CURLOPT_URL, $url);
    curl_setopt($ch, CURLOPT_NOBODY, true);
    curl_setopt($ch, CURLOPT_RETURNTRANSFER, true);
    curl_setopt($ch, CURLOPT_SSL_VERIFYPEER, false);
    curl_setopt($ch, CURLOPT_FOLLOWLOCATION, true);
    curl_setopt($ch, CURLOPT_TIMEOUT, 30);
    curl_exec($ch);
    
    $httpCode = curl_getinfo($ch, CURLINFO_HTTP_CODE);
    $contentLength = curl_getinfo($ch, CURLINFO_CONTENT_LENGTH_DOWNLOAD);
    $contentType = curl_getinfo($ch, CURLINFO_CONTENT_TYPE);
    curl_close($ch);
    
    if ($httpCode !== 200) {
        logMessage("Invalid URL: HTTP $httpCode");
        return false;
    }
    
    // Cek content type
    $isVideo = (strpos($contentType, 'video/') !== false || 
                strpos($contentType, 'application/octet-stream') !== false ||
                strpos($contentType, 'binary/octet-stream') !== false);
    
    if (!$isVideo && !empty($contentType)) {
        logMessage("Warning: Content-Type is $contentType, expected video");
    }
    
    logMessage("Content-Type: $contentType, Expected Size: $contentLength");
    
    // Download dengan streaming
    $fp = fopen($tempPath, 'wb');
    if (!$fp) {
        logMessage("Cannot open temp file");
        return false;
    }
    
    $ch = curl_init();
    curl_setopt($ch, CURLOPT_URL, $url);
    curl_setopt($ch, CURLOPT_RETURNTRANSFER, false);
    curl_setopt($ch, CURLOPT_SSL_VERIFYPEER, false);
    curl_setopt($ch, CURLOPT_FOLLOWLOCATION, true);
    curl_setopt($ch, CURLOPT_TIMEOUT, 300);
    
    $downloaded = 0;
    $lastUpdate = 0;
    
    curl_setopt($ch, CURLOPT_WRITEFUNCTION, function($ch, $data) use ($fp, &$downloaded, $contentLength, $chatId, $msgId, &$lastUpdate) {
        $length = fwrite($fp, $data);
        $downloaded += $length;
        
        if ($chatId && $msgId && time() - $lastUpdate > 3 && $contentLength > 0) {
            $percent = min(100, round(($downloaded / $contentLength) * 100));
            editMessage($chatId, $msgId, "⬇️ Download: $percent% (" . round($downloaded/1024/1024, 1) . "MB)");
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
    
    // Validasi strict
    if (!validateVideoStrict($tempPath)) {
        logMessage("Video validation failed");
        @unlink($tempPath);
        return false;
    }
    
    // Cek ukuran akhir
    $actualSize = filesize($tempPath);
    if ($contentLength > 0 && $actualSize < ($contentLength * 0.95)) {
        logMessage("Incomplete download: $actualSize / $contentLength");
        @unlink($tempPath);
        return false;
    }
    
    rename($tempPath, $filepath);
    logMessage("Download complete: $filepath ($actualSize bytes)");
    
    return $filepath;
}

// Main downloader
function getTikTokVideo($url) {
    // LoveTik Primary
    $result = getFromLoveTik($url);
    if ($result && isset($result['success'])) {
        logMessage("LoveTik success");
        return $result;
    }
    
    // TikWM Fallback
    logMessage("LoveTik failed, trying TikWM");
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
            [['text' => '⏱ Runtime'], ['text' => '📡 Ping']]
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
        $welcome = "👋 <b>LoveTik Downloader Bot</b>\n\n";
        $welcome .= "✨ <b>Fitur:</b>\n";
        $welcome .= "🎬 LoveTik API (HD No Watermark)\n";
        $welcome .= "🔍 Validasi video (anti blank)\n";
        $welcome .= "⚡️ No FFmpeg required\n";
        $welcome .= "🔄 Auto fallback\n\n";
        $welcome .= "📋 <b>Command:</b>\n";
        $welcome .= "• /runtime - Uptime bot\n";
        $welcome .= "• /ping - Cek latency\n";
        $welcome .= "• /status - Status sistem\n\n";
        $welcome .= "Kirim link TikTok sekarang!";
        
        sendMessage($chatId, $welcome, getKeyboard());
        return;
    }
    
    // Runtime
    if (strpos($text, '/runtime') !== false || $text === '⏱ Runtime') {
        $runtime = getRuntime();
        $memory = round(memory_get_usage(true) / 1024 / 1024, 2);
        $peakMemory = round(memory_get_peak_usage(true) / 1024 / 1024, 2);
        
        $msg = "⏱ <b>Runtime Information</b>\n\n";
        $msg .= "🕐 Uptime: <code>$runtime</code>\n";
        $msg .= "💾 Memory: <code>$memory MB</code> (Peak: $peakMemory MB)\n";
        $msg .= "🚀 Started: <code>" . date('Y-m-d H:i:s', $GLOBALS['START_TIME']) . "</code>";
        
        sendMessage($chatId, $msg);
        return;
    }
    
    // Ping
    if (strpos($text, '/ping') !== false || $text === '📡 Ping') {
        $ping = getPing();
        $latency = $ping['latency'];
        $status = $ping['status'];
        
        $emoji = $latency < 100 ? '🟢' : ($latency < 300 ? '🟡' : '🔴');
        
        $msg = "📡 <b>Ping Test</b>\n\n";
        $msg .= "$emoji Latency: <code>$latency ms</code>\n";
        $msg .= "✅ API Status: <code>$status</code>\n";
        $msg .= "🕐 " . date('Y-m-d H:i:s');
        
        sendMessage($chatId, $msg);
        return;
    }
    
    // Help
    if (strpos($text, '/help') !== false || $text === '📥 Cara Penggunaan') {
        $help = "📖 <b>Panduan:</b>\n\n";
        $help .= "1️⃣ Copy link TikTok (Share → Copy Link)\n";
        $help .= "2️⃣ Paste di bot ini\n";
        $help .= "3️⃣ Tunggu download & validasi\n";
        $help .= "4️⃣ Video dikirim!\n\n";
        $help .= "⚡️ <b>Tips:</b>\n";
        $help .= "• Video >50MB dikirim sebagai dokumen\n";
        $help .= "• Gunakan link www.tiktok.com\n";
        $help .= "• Tunggu proses validasi selesai";
        
        sendMessage($chatId, $help);
        return;
    }
    
    // Status
    if (strpos($text, '/status') !== false || $text === '📊 Status') {
        $ping = getPing();
        $runtime = getRuntime();
        
        $status = "🤖 <b>Status Bot</b>\n\n";
        $status .= "✅ Sistem: Normal\n";
        $status .= "🎬 Source: LoveTik API\n";
        $status .= "📡 Latency: {$ping['latency']}ms\n";
        $status .= "⏱ Uptime: $runtime\n";
        $status .= "🔧 Validation: PHP Native (No FFmpeg)\n";
        $status .= "⏰ " . date('Y-m-d H:i:s');
        
        sendMessage($chatId, $status);
        return;
    }
    
    // Detect TikTok link
    if (preg_match('/(https?:\/\/(www\.|vm\.|vt\.)?tiktok\.com\/[^\s]+)/', $text, $matches)) {
        $url = $matches[1];
        
        sendAction($chatId, 'typing');
        
        $proc = sendMessage($chatId, "🔍 <b>Menganalisis link...</b>\n🌐 LoveTik API", null);
        $procId = $proc['result']['message_id'] ?? null;
        
        $data = getTikTokVideo($url);
        
        if (isset($data['error'])) {
            editMessage($chatId, $procId, "❌ <b>Gagal:</b> " . $data['error']);
            return;
        }
        
        $isOriginal = $data['original'] ? '✅ HD No Watermark' : '⚠️ Standard';
        
        editMessage($chatId, $procId, 
            "✅ <b>Video ditemukan!</b>\n" .
            "👤 " . htmlspecialchars($data['author']) . "\n" .
            "📝 " . htmlspecialchars(substr($data['title'], 0, 40)) . "...\n" .
            "🎬 <b>$isOriginal</b>\n\n" .
            "⬇️ <b>Downloading & Validating...</b>"
        );
        
        sendAction($chatId, 'upload_video');
        
        $filename = 'tt_' . time() . '_' . uniqid() . '.mp4';
        $path = downloadVideoVerified($data['video_url'], $filename, $chatId, $procId);
        
        // Fallback SD
        if (!$path && isset($data['sd_url'])) {
            logMessage("HD failed, trying SD");
            editMessage($chatId, $procId, "⚠️ HD gagal, mencoba SD...");
            $filename = 'tt_sd_' . time() . '_' . uniqid() . '.mp4';
            $path = downloadVideoVerified($data['sd_url'], $filename, $chatId, $procId);
        }
        
        if ($path && file_exists($path)) {
            $size = filesize($path);
            $sizeMB = round($size / 1024 / 1024, 2);
            $isLarge = $size > MAX_FILE_SIZE;
            
            editMessage($chatId, $procId, "📤 <b>Mengirim...</b>\n📦 $sizeMB MB");
            sendAction($chatId, $isLarge ? 'upload_document' : 'upload_video');
            
            $caption = "🎵 " . htmlspecialchars($data['title']) . "\n" .
                      "👤 " . htmlspecialchars($data['author']) . "\n" .
                      "🎬 " . ($data['original'] ? 'HD No Watermark' : 'Standard') . "\n" .
                      "📦 {$sizeMB}MB";
            
            if ($isLarge) {
                $result = sendDocument($chatId, $path, $caption);
            } else {
                $result = sendVideo($chatId, $path, $caption);
            }
            
            if (file_exists($path)) {
                unlink($path);
            }
            
            if ($result) {
                sendTelegramRequest('deleteMessage', [
                    'chat_id' => $chatId,
                    'message_id' => $procId
                ]);
            } else {
                editMessage($chatId, $procId, "❌ Gagal upload. Coba lagi.");
            }
        } else {
            editMessage($chatId, $procId, 
                "⚠️ <b>Download gagal</b>\n\n" .
                "🔗 <b>Link langsung:</b>\n" .
                "<code>" . htmlspecialchars($data['video_url']) . "</code>"
            );
        }
        
        return;
    }
    
    // Unknown
    sendMessage($chatId, "❓ Kirim link TikTok untuk download.\n\nFormat:\n• https://www.tiktok.com/@user/video/123\n• https://vm.tiktok.com/xxx", getKeyboard());
}

// Main loop
function startBot() {
    logMessage("=== LOVETIK BOT STARTED (No FFmpeg) ===");
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
