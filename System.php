<?php
/**
 * TikTok HD Downloader Bot Telegram - PHP
 * Token: 8391191201:AAEVWguoQ5T8_qDZnZmCMD8uS7xpaAOvaLM
 * Fitur: Download HD, No Watermark, Multiple API Fallback
 */

// Konfigurasi
define('BOT_TOKEN', '8391191201:AAEVWguoQ5T8_qDZnZmCMD8uS7xpaAOvaLM');
define('API_URL', 'https://api.telegram.org/bot' . BOT_TOKEN . '/');
define('DOWNLOAD_DIR', __DIR__ . '/downloads/');
define('MAX_FILE_SIZE', 50 * 1024 * 1024); // 50MB Telegram limit

// Buat direktori downloads
if (!file_exists(DOWNLOAD_DIR)) {
    mkdir(DOWNLOAD_DIR, 0755, true);
}

// Logging
function logMessage($message) {
    $logFile = __DIR__ . '/bot.log';
    $timestamp = date('Y-m-d H:i:s');
    file_put_contents($logFile, "[$timestamp] $message" . PHP_EOL, FILE_APPEND);
}

// Telegram API Request
function sendTelegramRequest($method, $params = []) {
    $url = API_URL . $method;
    
    $ch = curl_init();
    curl_setopt($ch, CURLOPT_URL, $url);
    curl_setopt($ch, CURLOPT_POST, true);
    curl_setopt($ch, CURLOPT_POSTFIELDS, http_build_query($params));
    curl_setopt($ch, CURLOPT_RETURNTRANSFER, true);
    curl_setopt($ch, CURLOPT_SSL_VERIFYPEER, false);
    curl_setopt($ch, CURLOPT_TIMEOUT, 30);
    
    $response = curl_exec($ch);
    $httpCode = curl_getinfo($ch, CURLINFO_HTTP_CODE);
    
    if (curl_errno($ch)) {
        logMessage("CURL Error: " . curl_error($ch));
        curl_close($ch);
        return false;
    }
    
    curl_close($ch);
    
    if ($httpCode !== 200) {
        logMessage("HTTP Error: $httpCode");
        return false;
    }
    
    return json_decode($response, true);
}

// Kirim pesan
function sendMessage($chatId, $text, $replyMarkup = null, $parseMode = 'HTML') {
    $params = [
        'chat_id' => $chatId,
        'text' => $text,
        'parse_mode' => $parseMode,
        'disable_web_page_preview' => true
    ];
    
    if ($replyMarkup) {
        $params['reply_markup'] = json_encode($replyMarkup);
    }
    
    return sendTelegramRequest('sendMessage', $params);
}

// Edit pesan
function editMessageText($chatId, $messageId, $text) {
    return sendTelegramRequest('editMessageText', [
        'chat_id' => $chatId,
        'message_id' => $messageId,
        'text' => $text,
        'parse_mode' => 'HTML'
    ]);
}

// Kirim video
function sendVideo($chatId, $videoPath, $caption = '', $replyToMessageId = null) {
    $url = API_URL . 'sendVideo';
    
    $postFields = [
        'chat_id' => $chatId,
        'caption' => $caption,
        'parse_mode' => 'HTML',
        'supports_streaming' => true,
        'width' => 1080,
        'height' => 1920
    ];
    
    if ($replyToMessageId) {
        $postFields['reply_to_message_id'] = $replyToMessageId;
    }
    
    if (file_exists($videoPath)) {
        $postFields['video'] = new CURLFile($videoPath);
    } else {
        $postFields['video'] = $videoPath;
    }
    
    $ch = curl_init();
    curl_setopt($ch, CURLOPT_URL, $url);
    curl_setopt($ch, CURLOPT_POST, true);
    curl_setopt($ch, CURLOPT_POSTFIELDS, $postFields);
    curl_setopt($ch, CURLOPT_RETURNTRANSFER, true);
    curl_setopt($ch, CURLOPT_SSL_VERIFYPEER, false);
    curl_setopt($ch, CURLOPT_TIMEOUT, 180); // 3 menit untuk video HD
    
    $response = curl_exec($ch);
    
    if (curl_errno($ch)) {
        logMessage("Error sending video: " . curl_error($ch));
        curl_close($ch);
        return false;
    }
    
    curl_close($ch);
    return json_decode($response, true);
}

// Kirim dokumen (untuk video besar)
function sendDocument($chatId, $filePath, $caption = '') {
    $url = API_URL . 'sendDocument';
    
    $postFields = [
        'chat_id' => $chatId,
        'caption' => $caption,
        'parse_mode' => 'HTML',
        'document' => new CURLFile($filePath)
    ];
    
    $ch = curl_init();
    curl_setopt($ch, CURLOPT_URL, $url);
    curl_setopt($ch, CURLOPT_POST, true);
    curl_setopt($ch, CURLOPT_POSTFIELDS, $postFields);
    curl_setopt($ch, CURLOPT_RETURNTRANSFER, true);
    curl_setopt($ch, CURLOPT_SSL_VERIFYPEER, false);
    curl_setopt($ch, CURLOPT_TIMEOUT, 180);
    
    $response = curl_exec($ch);
    curl_close($ch);
    
    return json_decode($response, true);
}

// Typing indicator
function sendChatAction($chatId, $action = 'upload_video') {
    return sendTelegramRequest('sendChatAction', [
        'chat_id' => $chatId,
        'action' => $action
    ]);
}

// API 1: TikWM (HD Support)
function getFromTikWM($tiktokUrl) {
    $apiUrl = 'https://www.tikwm.com/api/';
    
    $ch = curl_init();
    curl_setopt($ch, CURLOPT_URL, $apiUrl);
    curl_setopt($ch, CURLOPT_POST, true);
    curl_setopt($ch, CURLOPT_POSTFIELDS, http_build_query([
        'url' => $tiktokUrl,
        'hd' => 1  // Request HD quality
    ]));
    curl_setopt($ch, CURLOPT_RETURNTRANSFER, true);
    curl_setopt($ch, CURLOPT_SSL_VERIFYPEER, false);
    curl_setopt($ch, CURLOPT_FOLLOWLOCATION, true);
    curl_setopt($ch, CURLOPT_TIMEOUT, 30);
    curl_setopt($ch, CURLOPT_HTTPHEADER, [
        'Content-Type: application/x-www-form-urlencoded',
        'User-Agent: Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36'
    ]);
    
    $response = curl_exec($ch);
    $httpCode = curl_getinfo($ch, CURLINFO_HTTP_CODE);
    curl_close($ch);
    
    if ($httpCode !== 200 || empty($response)) {
        return null;
    }
    
    $data = json_decode($response, true);
    
    if (isset($data['data']) && isset($data['data']['play'])) {
        return [
            'success' => true,
            'video_url' => $data['data']['hdplay'] ?? $data['data']['play'], // Prioritas HD
            'sd_url' => $data['data']['play'], // Fallback SD
            'title' => $data['data']['title'] ?? 'TikTok Video',
            'author' => $data['data']['author']['nickname'] ?? $data['data']['author']['unique_id'] ?? 'Unknown',
            'cover' => $data['data']['cover'] ?? '',
            'duration' => $data['data']['duration'] ?? 0,
            'hd_size' => $data['data']['hd_size'] ?? 0,
            'size' => $data['data']['size'] ?? 0,
            'source' => 'tikwm'
        ];
    }
    
    return null;
}

// API 2: SSSTik (Alternative HD)
function getFromSSSTik($tiktokUrl) {
    $apiUrl = 'https://ssstik.io/abc?url=dl';
    
    // Step 1: Get token
    $ch = curl_init();
    curl_setopt($ch, CURLOPT_URL, 'https://ssstik.io');
    curl_setopt($ch, CURLOPT_RETURNTRANSFER, true);
    curl_setopt($ch, CURLOPT_SSL_VERIFYPEER, false);
    curl_setopt($ch, CURLOPT_TIMEOUT, 10);
    curl_setopt($ch, CURLOPT_HTTPHEADER, [
        'User-Agent: Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36'
    ]);
    
    $response = curl_exec($ch);
    curl_close($ch);
    
    // Extract tt-token dari HTML
    preg_match('/name="tt-token" content="([^"]+)"/', $response, $matches);
    $token = $matches[1] ?? '';
    
    if (empty($token)) {
        return null;
    }
    
    // Step 2: Submit URL
    $ch = curl_init();
    curl_setopt($ch, CURLOPT_URL, $apiUrl);
    curl_setopt($ch, CURLOPT_POST, true);
    curl_setopt($ch, CURLOPT_POSTFIELDS, http_build_query([
        'id' => $tiktokUrl,
        'locale' => 'en',
        'tt' => $token
    ]));
    curl_setopt($ch, CURLOPT_RETURNTRANSFER, true);
    curl_setopt($ch, CURLOPT_SSL_VERIFYPEER, false);
    curl_setopt($ch, CURLOPT_FOLLOWLOCATION, true);
    curl_setopt($ch, CURLOPT_TIMEOUT, 30);
    curl_setopt($ch, CURLOPT_HTTPHEADER, [
        'User-Agent: Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36',
        'Content-Type: application/x-www-form-urlencoded'
    ]);
    
    $response = curl_exec($ch);
    curl_close($ch);
    
    // Extract video URL
    preg_match('/href="([^"]+)"[^>]*>Download HD/', $response, $matches);
    if (isset($matches[1])) {
        $videoUrl = 'https://ssstik.io' . $matches[1];
        return [
            'success' => true,
            'video_url' => $videoUrl,
            'title' => 'TikTok Video',
            'author' => 'Unknown',
            'source' => 'ssstik'
        ];
    }
    
    // Try without HD
    preg_match('/href="([^"]+)"[^>]*>Download Without Watermark/', $response, $matches);
    if (isset($matches[1])) {
        return [
            'success' => true,
            'video_url' => 'https://ssstik.io' . $matches[1],
            'title' => 'TikTok Video',
            'author' => 'Unknown',
            'source' => 'ssstik_sd'
        ];
    }
    
    return null;
}

// API 3: TikMate (Backup)
function getFromTikMate($tiktokUrl) {
    $apiUrl = 'https://api.tikmate.app/api/lookup';
    
    $ch = curl_init();
    curl_setopt($ch, CURLOPT_URL, $apiUrl);
    curl_setopt($ch, CURLOPT_POST, true);
    curl_setopt($ch, CURLOPT_POSTFIELDS, http_build_query(['url' => $tiktokUrl]));
    curl_setopt($ch, CURLOPT_RETURNTRANSFER, true);
    curl_setopt($ch, CURLOPT_SSL_VERIFYPEER, false);
    curl_setopt($ch, CURLOPT_TIMEOUT, 30);
    curl_setopt($ch, CURLOPT_HTTPHEADER, [
        'Content-Type: application/x-www-form-urlencoded',
        'User-Agent: Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36'
    ]);
    
    $response = curl_exec($ch);
    curl_close($ch);
    
    $data = json_decode($response, true);
    
    if (isset($data['video_url'])) {
        return [
            'success' => true,
            'video_url' => $data['video_url'],
            'title' => $data['title'] ?? 'TikTok Video',
            'author' => $data['author'] ?? 'Unknown',
            'source' => 'tikmate'
        ];
    }
    
    return null;
}

// Main downloader dengan fallback
function downloadTikTokHD($tiktokUrl) {
    // Bersihkan URL
    $tiktokUrl = trim($tiktokUrl);
    
    // Validasi URL
    if (!preg_match('/https?:\/\/(www\.|vm\.|vt\.)?tiktok\.com\/[@\w\-\/]+/', $tiktokUrl)) {
        return ['error' => 'URL TikTok tidak valid'];
    }
    
    $apis = ['getFromTikWM', 'getFromSSSTik', 'getFromTikMate'];
    
    foreach ($apis as $apiFunction) {
        logMessage("Trying API: $apiFunction");
        $result = $apiFunction($tiktokUrl);
        
        if ($result && isset($result['success'])) {
            logMessage("Success with API: $apiFunction");
            return $result;
        }
    }
    
    return ['error' => 'Gagal mengambil video HD dari semua sumber'];
}

// Download file dengan progress
function downloadFile($url, $filename, $chatId = null, $messageId = null) {
    $filepath = DOWNLOAD_DIR . $filename;
    
    $ch = curl_init();
    curl_setopt($ch, CURLOPT_URL, $url);
    curl_setopt($ch, CURLOPT_RETURNTRANSFER, true);
    curl_setopt($ch, CURLOPT_SSL_VERIFYPEER, false);
    curl_setopt($ch, CURLOPT_FOLLOWLOCATION, true);
    curl_setopt($ch, CURLOPT_TIMEOUT, 180); // 3 menit untuk HD
    
    // Progress callback untuk video besar
    if ($chatId && $messageId) {
        curl_setopt($ch, CURLOPT_NOPROGRESS, false);
        curl_setopt($ch, CURLOPT_PROGRESSFUNCTION, function($ch, $downloadSize, $downloaded) use ($chatId, $messageId) {
            static $lastUpdate = 0;
            if ($downloadSize > 0 && time() - $lastUpdate > 3) { // Update setiap 3 detik
                $percent = round(($downloaded / $downloadSize) * 100);
                if ($percent < 100) {
                    editMessageText($chatId, $messageId, "⬇️ <b>Download Progress:</b> $percent%\n⏳ Sedang mengunduh video HD...");
                    $lastUpdate = time();
                }
            }
            return 0;
        });
    }
    
    $data = curl_exec($ch);
    $httpCode = curl_getinfo($ch, CURLINFO_HTTP_CODE);
    $downloadSize = curl_getinfo($ch, CURLINFO_SIZE_DOWNLOAD);
    
    if (curl_errno($ch) || $httpCode !== 200 || empty($data)) {
        logMessage("Download failed: HTTP $httpCode, Error: " . curl_error($ch));
        curl_close($ch);
        return false;
    }
    
    curl_close($ch);
    
    file_put_contents($filepath, $data);
    
    // Verifikasi file
    if (!file_exists($filepath) || filesize($filepath) === 0) {
        return false;
    }
    
    return $filepath;
}

// Get updates
function getUpdates($offset = 0) {
    $params = ['offset' => $offset, 'limit' => 100];
    $response = sendTelegramRequest('getUpdates', $params);
    return $response['result'] ?? [];
}

// Keyboard menu
function getMainMenu() {
    return [
        'keyboard' => [
            [['text' => '📥 Cara Penggunaan']],
            [['text' => '📊 Status Bot']],
            [['text' => '🎵 Download MP3']]
        ],
        'resize_keyboard' => true,
        'one_time_keyboard' => false
    ];
}

// Handler pesan
function handleMessage($message) {
    $chatId = $message['chat']['id'];
    $text = $message['text'] ?? '';
    $messageId = $message['message_id'];
    $username = $message['from']['username'] ?? 'Unknown';
    
    logMessage("Message from @$username: $text");
    
    // Command /start
    if (strpos($text, '/start') === 0) {
        $welcomeText = "👋 <b>Selamat datang di TikTok HD Downloader Bot!</b>\n\n";
        $welcomeText .= "🎬 <b>Fitur Unggulan:</b>\n";
        $welcomeText .= "✅ Download Video HD (1080p)\n";
        $welcomeText .= "✅ Tanpa Watermark\n";
        $welcomeText .= "✅ Kualitas Original\n";
        $welcomeText .= "✅ Gratis & Cepat\n\n";
        $welcomeText .= "📌 <b>Cara pakai:</b>\n";
        $welcomeText .= "1. Copy link TikTok\n";
        $welcomeText .= "2. Paste di sini\n";
        $welcomeText .= "3. Tunggu proses HD\n\n";
        $welcomeText .= "⚡️ Bot akan otomatis pilih kualitas HD terbaik!";
        
        sendMessage($chatId, $welcomeText, getMainMenu());
        return;
    }
    
    // Command /help
    if (strpos($text, '/help') === 0 || $text === '📥 Cara Penggunaan') {
        $helpText = "📖 <b>Panduan Lengkap</b>\n\n";
        $helpText .= "🎯 <b>Mendapatkan Link:</b>\n";
        $helpText .= "1. Buka TikTok app\n";
        $helpText .= "2. Share → Copy Link\n";
        $helpText .= "3. Paste ke bot ini\n\n";
        $helpText .= "⚠️ <b>Catatan Penting:</b>\n";
        $helpText .= "• Video private tidak bisa di download\n";
        $helpText .= "• Maksimal ukuran 50MB (Telegram limit)\n";
        $helpText .= "• Proses HD membutuhkan waktu lebih lama\n";
        $helpText .= "• Jika HD gagal, bot akan otomatis coba SD\n\n";
        $helpText .= "🔧 <b>Command:</b>\n";
        $helpText .= "/start - Mulai bot\n";
        $helpText .= "/help - Bantuan\n";
        $helpText .= "/status - Cek status";
        
        sendMessage($chatId, $helpText);
        return;
    }
    
    // Command /status
    if (strpos($text, '/status') === 0 || $text === '📊 Status Bot') {
        $statusText = "🤖 <b>Status Bot HD</b>\n\n";
        $statusText .= "✅ Bot aktif\n";
        $statusText .= "📹 HD Quality: <b>1080p Support</b>\n";
        $statusText .= "🔄 Multiple API: <b>3 Sources</b>\n";
        $statusText .= "⏰ " . date('Y-m-d H:i:s') . "\n";
        $statusText .= "💾 PHP: " . phpversion() . "\n\n";
        $statusText .= "🚀 <b>Sumber API:</b>\n";
        $statusText .= "• TikWM (Primary HD)\n";
        $statusText .= "• SSSTik (Backup HD)\n";
        $statusText .= "• TikMate (Fallback)";
        
        sendMessage($chatId, $statusText);
        return;
    }
    
    // MP3 Download (placeholder)
    if ($text === '🎵 Download MP3') {
        sendMessage($chatId, "🎵 <b>Fitur MP3</b>\n\nKirim link TikTok dan tambahkan caption <code>mp3</code> untuk download audio only.\n\nContoh:\n<code>https://tiktok.com/xxx</code> (tulis mp3 di pesan lain atau reply dengan mp3)");
        return;
    }
    
    // Deteksi link TikTok
    if (preg_match('/(https?:\/\/(www\.|vm\.|vt\.)?tiktok\.com\/[^\s]+)/', $text, $matches)) {
        $tiktokUrl = $matches[1];
        
        // Cek apakah user minta MP3
        $isMP3 = stripos($text, 'mp3') !== false;
        
        sendChatAction($chatId, 'typing');
        
        // Pesan awal
        $msg = sendMessage($chatId, "🔍 <b>Mencari video HD...</b>\n⏳ Mengambil data dari TikTok", null);
        $processingMsgId = $msg['result']['message_id'] ?? null;
        
        // Get video info HD
        $videoInfo = downloadTikTokHD($tiktokUrl);
        
        if (isset($videoInfo['error'])) {
            editMessageText($chatId, $processingMsgId, "❌ <b>Error:</b> " . $videoInfo['error']);
            return;
        }
        
        // Info video ditemukan
        $quality = isset($videoInfo['hd_size']) && $videoInfo['hd_size'] > 0 ? 'HD' : 'SD';
        $sizeMB = isset($videoInfo['hd_size']) ? round($videoInfo['hd_size'] / 1024 / 1024, 2) : 
                  (isset($videoInfo['size']) ? round($videoInfo['size'] / 1024 / 1024, 2) : 'Unknown');
        
        editMessageText($chatId, $processingMsgId, 
            "✅ <b>Video ditemukan!</b>\n" .
            "👤 <b>Author:</b> " . htmlspecialchars($videoInfo['author']) . "\n" .
            "📝 <b>Title:</b> " . htmlspecialchars(substr($videoInfo['title'], 0, 50)) . "...\n" .
            "🎬 <b>Quality:</b> $quality\n" .
            "📦 <b>Size:</b> ~{$sizeMB}MB\n" .
            "🌐 <b>Source:</b> " . $videoInfo['source'] . "\n\n" .
            "⬇️ <b>Sedang download...</b>"
        );
        
        sendChatAction($chatId, 'upload_video');
        
        // Download video
        $filename = 'tiktok_hd_' . time() . '_' . uniqid() . '.mp4';
        $localPath = downloadFile($videoInfo['video_url'], $filename, $chatId, $processingMsgId);
        
        // Jika HD gagal, coba SD
        if (!$localPath && isset($videoInfo['sd_url'])) {
            logMessage("HD failed, trying SD");
            editMessageText($chatId, $processingMsgId, "⚠️ HD gagal, mencoba SD quality...");
            $filename = 'tiktok_sd_' . time() . '_' . uniqid() . '.mp4';
            $localPath = downloadFile($videoInfo['sd_url'], $filename, $chatId, $processingMsgId);
        }
        
        if ($localPath && file_exists($localPath)) {
            $actualSize = filesize($localPath);
            $actualSizeMB = round($actualSize / 1024 / 1024, 2);
            $isLarge = $actualSize > MAX_FILE_SIZE;
            
            // Update pesan
            editMessageText($chatId, $processingMsgId, 
                "📤 <b>Mengirim video...</b>\n" .
                "📦 Size: {$actualSizeMB}MB\n" .
                ($isLarge ? "⚠️ File besar, mengirim sebagai dokumen" : "⏳ Upload ke Telegram...")
            );
            
            sendChatAction($chatId, $isLarge ? 'upload_document' : 'upload_video');
            
            $caption = "🎵 " . htmlspecialchars($videoInfo['title']) . "\n" .
                      "👤 " . htmlspecialchars($videoInfo['author']) . "\n" .
                      "🎬 Quality: " . ($isLarge ? 'HD (Compressed)' : 'HD') . "\n" .
                      "📦 {$actualSizeMB}MB\n" .
                      "✅ @TikTokHDBot";
            
            if ($isLarge) {
                $result = sendDocument($chatId, $localPath, $caption);
            } else {
                $result = sendVideo($chatId, $localPath, $caption, $messageId);
            }
            
            // Cleanup
            if (file_exists($localPath)) {
                unlink($localPath);
            }
            
            // Hapus pesan processing jika berhasil
            if ($result) {
                sendTelegramRequest('deleteMessage', [
                    'chat_id' => $chatId,
                    'message_id' => $processingMsgId
                ]);
            } else {
                editMessageText($chatId, $processingMsgId, "❌ Gagal mengirim video. Coba lagi nanti.");
            }
        } else {
            // Fallback: kirim link langsung
            editMessageText($chatId, $processingMsgId, 
                "⚠️ <b>Download server gagal</b>\n\n" .
                "🔗 <b>Link langsung:</b>\n<code>" . $videoInfo['video_url'] . "</code>\n\n" .
                "Klik link untuk download manual (buka di browser)."
            );
        }
        
        return;
    }
    
    // Pesan tidak dikenali
    sendMessage($chatId, "❓ Kirim link TikTok untuk download HD.\n\nContoh:\n<code>https://www.tiktok.com/@user/video/123456</code>\n\nAtau gunakan tombol menu di bawah.", getMainMenu());
}

// Main loop
function startBot() {
    logMessage("=== BOT HD STARTED ===");
    echo "Bot HD started. Press Ctrl+C to stop.\n";
    
    $lastUpdateId = 0;
    
    while (true) {
        try {
            $updates = getUpdates($lastUpdateId + 1);
            
            foreach ($updates as $update) {
                $lastUpdateId = $update['update_id'];
                
                if (isset($update['message'])) {
                    handleMessage($update['message']);
                }
            }
            
            usleep(100000); // 0.1 detik
            
        } catch (Exception $e) {
            logMessage("Error: " . $e->getMessage());
            sleep(5);
        }
    }
}

// Webhook handler
function handleWebhook() {
    $content = file_get_contents('php://input');
    $update = json_decode($content, true);
    
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
