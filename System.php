<?php
/**
 * TikTok Downloader Bot Telegram - PHP
 * Token: 8391191201:AAEVWguoQ5T8_qDZnZmCMD8uS7xpaAOvaLM
 */

// Konfigurasi
define('BOT_TOKEN', '8391191201:AAEVWguoQ5T8_qDZnZmCMD8uS7xpaAOvaLM');
define('API_URL', 'https://api.telegram.org/bot' . BOT_TOKEN . '/');
define('DOWNLOAD_DIR', __DIR__ . '/downloads/');

// Buat direktori downloads jika belum ada
if (!file_exists(DOWNLOAD_DIR)) {
    mkdir(DOWNLOAD_DIR, 0755, true);
}

// Logging
function logMessage($message) {
    $logFile = __DIR__ . '/bot.log';
    $timestamp = date('Y-m-d H:i:s');
    file_put_contents($logFile, "[$timestamp] $message" . PHP_EOL, FILE_APPEND);
}

// Fungsi untuk mengirim request ke Telegram API
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

// Fungsi untuk mengirim pesan
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

// Fungsi untuk mengirim video
function sendVideo($chatId, $videoPath, $caption = '', $replyToMessageId = null) {
    $url = API_URL . 'sendVideo';
    
    $postFields = [
        'chat_id' => $chatId,
        'caption' => $caption,
        'parse_mode' => 'HTML',
        'supports_streaming' => true
    ];
    
    if ($replyToMessageId) {
        $postFields['reply_to_message_id'] = $replyToMessageId;
    }
    
    if (file_exists($videoPath)) {
        $postFields['video'] = new CURLFile($videoPath);
    } else {
        // Jika file lokal tidak ada, coba kirim sebagai URL
        $postFields['video'] = $videoPath;
        unset($postFields['video']);
        $postFields['video'] = $videoPath;
    }
    
    $ch = curl_init();
    curl_setopt($ch, CURLOPT_URL, $url);
    curl_setopt($ch, CURLOPT_POST, true);
    curl_setopt($ch, CURLOPT_POSTFIELDS, $postFields);
    curl_setopt($ch, CURLOPT_RETURNTRANSFER, true);
    curl_setopt($ch, CURLOPT_SSL_VERIFYPEER, false);
    curl_setopt($ch, CURLOPT_TIMEOUT, 120); // Timeout lebih lama untuk upload video
    
    $response = curl_exec($ch);
    
    if (curl_errno($ch)) {
        logMessage("Error sending video: " . curl_error($ch));
        curl_close($ch);
        return false;
    }
    
    curl_close($ch);
    return json_decode($response, true);
}

// Fungsi untuk mengirim dokumen (untuk video besar)
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
    curl_setopt($ch, CURLOPT_TIMEOUT, 120);
    
    $response = curl_exec($ch);
    curl_close($ch);
    
    return json_decode($response, true);
}

// Fungsi untuk menampilkan typing indicator
function sendChatAction($chatId, $action = 'upload_video') {
    return sendTelegramRequest('sendChatAction', [
        'chat_id' => $chatId,
        'action' => $action
    ]);
}

// Fungsi untuk download TikTok menggunakan RapidAPI (pilihan API)
function downloadTikTokVideo($tiktokUrl) {
    // Bersihkan URL
    $tiktokUrl = trim($tiktokUrl);
    
    // Validasi URL TikTok
    if (!preg_match('/https?:\/\/(www\.|vm\.|vt\.)?tiktok\.com\/[@\w\-\/]+/', $tiktokUrl)) {
        return ['error' => 'URL TikTok tidak valid'];
    }
    
    // Method 1: Menggunakan TikTok API Downloader (tanpa API key)
    $apiEndpoints = [
        // API 1: tikwm.com API
        [
            'url' => 'https://www.tikwm.com/api/',
            'method' => 'POST',
            'params' => ['url' => $tiktokUrl, 'hd' => 1],
            'parser' => function($response) {
                $data = json_decode($response, true);
                if (isset($data['data']['play'])) {
                    return [
                        'video_url' => $data['data']['play'],
                        'hd_video_url' => $data['data']['hdplay'] ?? $data['data']['play'],
                        'title' => $data['data']['title'] ?? 'TikTok Video',
                        'author' => $data['data']['author']['nickname'] ?? 'Unknown',
                        'cover' => $data['data']['cover'] ?? '',
                        'duration' => $data['data']['duration'] ?? 0
                    ];
                }
                return null;
            }
        ],
        // API 2: ttdownloader (backup)
        [
            'url' => 'https://api.tikmate.app/api/lookup',
            'method' => 'POST',
            'params' => ['url' => $tiktokUrl],
            'headers' => ['Content-Type: application/x-www-form-urlencoded'],
            'parser' => function($response) {
                $data = json_decode($response, true);
                if (isset($data['video_url'])) {
                    return [
                        'video_url' => $data['video_url'],
                        'title' => $data['title'] ?? 'TikTok Video',
                        'author' => $data['author'] ?? 'Unknown'
                    ];
                }
                return null;
            }
        ]
    ];
    
    foreach ($apiEndpoints as $api) {
        try {
            $ch = curl_init();
            curl_setopt($ch, CURLOPT_URL, $api['url']);
            curl_setopt($ch, CURLOPT_RETURNTRANSFER, true);
            curl_setopt($ch, CURLOPT_SSL_VERIFYPEER, false);
            curl_setopt($ch, CURLOPT_FOLLOWLOCATION, true);
            curl_setopt($ch, CURLOPT_TIMEOUT, 30);
            
            if ($api['method'] === 'POST') {
                curl_setopt($ch, CURLOPT_POST, true);
                curl_setopt($ch, CURLOPT_POSTFIELDS, http_build_query($api['params']));
            }
            
            if (isset($api['headers'])) {
                curl_setopt($ch, CURLOPT_HTTPHEADER, $api['headers']);
            }
            
            $response = curl_exec($ch);
            $httpCode = curl_getinfo($ch, CURLINFO_HTTP_CODE);
            curl_close($ch);
            
            if ($httpCode === 200 && !empty($response)) {
                $result = $api['parser']($response);
                if ($result !== null) {
                    return $result;
                }
            }
        } catch (Exception $e) {
            logMessage("API Error: " . $e->getMessage());
            continue;
        }
    }
    
    return ['error' => 'Gagal mengambil video dari semua sumber'];
}

// Fungsi untuk download file ke server lokal
function downloadFile($url, $filename) {
    $filepath = DOWNLOAD_DIR . $filename;
    
    $ch = curl_init();
    curl_setopt($ch, CURLOPT_URL, $url);
    curl_setopt($ch, CURLOPT_RETURNTRANSFER, true);
    curl_setopt($ch, CURLOPT_SSL_VERIFYPEER, false);
    curl_setopt($ch, CURLOPT_FOLLOWLOCATION, true);
    curl_setopt($ch, CURLOPT_TIMEOUT, 120);
    
    $data = curl_exec($ch);
    $httpCode = curl_getinfo($ch, CURLINFO_HTTP_CODE);
    
    if (curl_errno($ch) || $httpCode !== 200) {
        curl_close($ch);
        return false;
    }
    
    curl_close($ch);
    
    file_put_contents($filepath, $data);
    return $filepath;
}

// Fungsi untuk mendapatkan update dari Telegram
function getUpdates($offset = 0) {
    $params = ['offset' => $offset, 'limit' => 100];
    $response = sendTelegramRequest('getUpdates', $params);
    
    return $response['result'] ?? [];
}

// Fungsi untuk membuat keyboard menu
function getMainMenu() {
    return [
        'keyboard' => [
            [['text' => '📥 Cara Penggunaan']],
            [['text' => '📊 Status Bot']]
        ],
        'resize_keyboard' => true,
        'one_time_keyboard' => false
    ];
}

// Handler untuk pesan
function handleMessage($message) {
    $chatId = $message['chat']['id'];
    $text = $message['text'] ?? '';
    $messageId = $message['message_id'];
    $username = $message['from']['username'] ?? 'Unknown';
    
    logMessage("Message from @$username: $text");
    
    // Command /start
    if (strpos($text, '/start') === 0) {
        $welcomeText = "👋 <b>Selamat datang di TikTok Downloader Bot!</b>\n\n";
        $welcomeText .= "🎵 <b>Cara menggunakan:</b>\n";
        $welcomeText .= "1. Copy link video TikTok yang ingin diunduh\n";
        $welcomeText .= "2. Paste link ke bot ini\n";
        $welcomeText .= "3. Tunggu proses download\n";
        $welcomeText .= "4. Video akan dikirim ke chat ini\n\n";
        $welcomeText .= "📌 <b>Format link yang didukung:</b>\n";
        $welcomeText .= "• https://www.tiktok.com/@user/video/123456\n";
        $welcomeText .= "• https://vm.tiktok.com/xxxxx\n";
        $welcomeText .= "• https://vt.tiktok.com/xxxxx\n\n";
        $welcomeText .= "⚡️ Bot ini gratis dan tanpa watermark!";
        
        sendMessage($chatId, $welcomeText, getMainMenu());
        return;
    }
    
    // Command /help atau tombol cara penggunaan
    if (strpos($text, '/help') === 0 || $text === '📥 Cara Penggunaan') {
        $helpText = "📖 <b>Panduan Penggunaan</b>\n\n";
        $helpText .= "1️⃣ Buka aplikasi TikTok\n";
        $helpText .= "2️⃣ Cari video yang ingin diunduh\n";
        $helpText .= "3️⃣ Klik tombol 'Share' (Bagikan)\n";
        $helpText .= "4️⃣ Pilih 'Copy Link'\n";
        $helpText .= "5️⃣ Kembali ke Telegram dan paste link ke bot ini\n";
        $helpText .= "6️⃣ Tunggu beberapa saat hingga video dikirim\n\n";
        $helpText .= "❗️ <b>Catatan:</b>\n";
        $helpText .= "• Pastikan link TikTok valid\n";
        $helpText .= "• Video private tidak dapat diunduh\n";
        $helpText .= "• Ukuran video maksimal 50MB untuk Telegram";
        
        sendMessage($chatId, $helpText);
        return;
    }
    
    // Command /status atau tombol status
    if (strpos($text, '/status') === 0 || $text === '📊 Status Bot') {
        $statusText = "🤖 <b>Status Bot</b>\n\n";
        $statusText .= "✅ Bot aktif dan berjalan normal\n";
        $statusText .= "📱 Server: " . php_uname('n') . "\n";
        $statusText .= "⏰ Waktu: " . date('Y-m-d H:i:s') . "\n";
        $statusText .= "💾 PHP Version: " . phpversion() . "\n";
        
        sendMessage($chatId, $statusText);
        return;
    }
    
    // Deteksi link TikTok
    if (preg_match('/(https?:\/\/(www\.|vm\.|vt\.)?tiktok\.com\/[^\s]+)/', $text, $matches)) {
        $tiktokUrl = $matches[1];
        
        // Kirim typing indicator
        sendChatAction($chatId, 'typing');
        
        // Pesan sedang memproses
        $processingMsg = sendMessage($chatId, "⏳ <b>Sedang memproses...</b>\nMengambil informasi video TikTok...", null);
        
        // Download info
        $videoInfo = downloadTikTokVideo($tiktokUrl);
        
        if (isset($videoInfo['error'])) {
            sendMessage($chatId, "❌ <b>Error:</b> " . $videoInfo['error'] . "\n\nCoba lagi dengan link yang berbeda atau pastikan video tidak private.");
            return;
        }
        
        // Update pesan
        sendMessage($chatId, "📥 <b>Video ditemukan!</b>\n👤 Author: " . htmlspecialchars($videoInfo['author']) . "\n📝 Title: " . htmlspecialchars(substr($videoInfo['title'], 0, 100)) . "...\n\n⬇️ Sedang mengunduh video...", null);
        
        // Kirim action upload
        sendChatAction($chatId, 'upload_video');
        
        // Download video ke server lokal
        $filename = 'tiktok_' . time() . '_' . uniqid() . '.mp4';
        $localPath = downloadFile($videoInfo['video_url'], $filename);
        
        if ($localPath && file_exists($localPath)) {
            $fileSize = filesize($localPath);
            $sizeMB = round($fileSize / 1024 / 1024, 2);
            
            // Cek ukuran file (Telegram limit 50MB untuk bot)
            if ($fileSize > 50 * 1024 * 1024) {
                // Kirim sebagai dokumen jika terlalu besar
                sendMessage($chatId, "📦 Video terlalu besar ($sizeMB MB), mengirim sebagai dokumen...", null);
                sendChatAction($chatId, 'upload_document');
                
                $caption = "🎵 " . htmlspecialchars($videoInfo['title']) . "\n👤 " . htmlspecialchars($videoInfo['author']) . "\n📦 Size: $sizeMB MB";
                $result = sendDocument($chatId, $localPath, $caption);
            } else {
                // Kirim sebagai video
                $caption = "🎵 " . htmlspecialchars($videoInfo['title']) . "\n👤 " . htmlspecialchars($videoInfo['author']) . "\n📦 Size: $sizeMB MB\n\n✅ Downloaded by @TikTokDownloaderBot";
                $result = sendVideo($chatId, $localPath, $caption, $messageId);
            }
            
            // Hapus file lokal setelah dikirim
            if (file_exists($localPath)) {
                unlink($localPath);
            }
            
            if (!$result) {
                sendMessage($chatId, "❌ Gagal mengirim video. Mencoba metode alternatif...", null);
                // Fallback: kirim link langsung
                sendMessage($chatId, "🔗 <b>Link Video:</b>\n" . $videoInfo['video_url'] . "\n\nKlik link di atas untuk mengunduh manual.");
            }
        } else {
            // Jika gagal download lokal, kirim link langsung
            sendMessage($chatId, "⚠️ <b>Video siap!</b>\n\nKlik link berikut untuk mengunduh:\n" . $videoInfo['video_url'] . "\n\n📝 " . htmlspecialchars($videoInfo['title']));
        }
        
        return;
    }
    
    // Pesan tidak dikenali
    sendMessage($chatId, "❓ Saya tidak mengerti pesan tersebut.\n\nKirim link TikTok untuk mendownload video, atau gunakan /help untuk bantuan.", getMainMenu());
}

// Main loop untuk polling
function startBot() {
    logMessage("Bot started...");
    echo "Bot started. Press Ctrl+C to stop.\n";
    
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
            
            // Sleep untuk menghindari rate limit
            usleep(100000); // 0.1 detik
            
        } catch (Exception $e) {
            logMessage("Error in main loop: " . $e->getMessage());
            sleep(5);
        }
    }
}

// Webhook handler untuk mode webhook
function handleWebhook() {
    $content = file_get_contents('php://input');
    $update = json_decode($content, true);
    
    if (isset($update['message'])) {
        handleMessage($update['message']);
    }
    
    http_response_code(200);
    echo 'OK';
}

// Mode eksekusi
if (php_sapi_name() === 'cli') {
    // Mode CLI - Long polling
    startBot();
} else {
    // Mode Web - Webhook
    handleWebhook();
}
