<?php
/**
 * Bot Telegram PHP - Auto Create Topics dari API AnimeKita
 * 
 * Cara pakai:
 * 1. Upload ke hosting/server dengan PHP 7.4+
 * 2. Set webhook: https://api.telegram.org/bot<TOKEN>/setWebhook?url=<URL_SCRIPT>
 * 3. Atau jalankan polling mode dengan cronjob/curl loop
 */

// Konfigurasi
define('BOT_TOKEN', '8391191201:AAFKUW9n23EYzIH9O-9JCvJc1jO5t3n2a28'); // HI LOSER, WELCOME if u can hack this
define('API_URL', 'https://apps.animekita.org/api/v1.1.9//anime-list.php');
define('BASE_URL', 'https://api.telegram.org/bot' . BOT_TOKEN . '/');

// Fungsi untuk mengirim request ke Telegram API
function telegramRequest($method, $params = []) {
    $url = BASE_URL . $method;
    
    $ch = curl_init();
    curl_setopt($ch, CURLOPT_URL, $url);
    curl_setopt($ch, CURLOPT_POST, true);
    curl_setopt($ch, CURLOPT_POSTFIELDS, http_build_query($params));
    curl_setopt($ch, CURLOPT_RETURNTRANSFER, true);
    curl_setopt($ch, CURLOPT_SSL_VERIFYPEER, false);
    
    $response = curl_exec($ch);
    $httpCode = curl_getinfo($ch, CURLINFO_HTTP_CODE);
    curl_close($ch);
    
    if ($httpCode == 200) {
        return json_decode($response, true);
    }
    
    return ['ok' => false, 'error' => $response];
}

// Fungsi untuk mengambil data dari API AnimeKita
function getAnimeData() {
    $ch = curl_init();
    curl_setopt($ch, CURLOPT_URL, API_URL);
    curl_setopt($ch, CURLOPT_RETURNTRANSFER, true);
    curl_setopt($ch, CURLOPT_FOLLOWLOCATION, true);
    curl_setopt($ch, CURLOPT_TIMEOUT, 30);
    curl_setopt($ch, CURLOPT_SSL_VERIFYPEER, false);
    
    $response = curl_exec($ch);
    $httpCode = curl_getinfo($ch, CURLINFO_HTTP_CODE);
    curl_close($ch);
    
    if ($httpCode == 200) {
        $data = json_decode($response, true);
        return $data;
    }
    
    return null;
}

// Fungsi untuk membuat topic di grup
function createForumTopic($chatId, $name) {
    return telegramRequest('createForumTopic', [
        'chat_id' => $chatId,
        'name' => substr($name, 0, 128) // Max 128 karakter
    ]);
}

// Fungsi untuk kirim pesan ke topic
function sendMessageToTopic($chatId, $topicId, $text, $parseMode = 'Markdown') {
    return telegramRequest('sendMessage', [
        'chat_id' => $chatId,
        'message_thread_id' => $topicId,
        'text' => $text,
        'parse_mode' => $parseMode
    ]);
}

// Fungsi untuk kirim foto ke topic
function sendPhotoToTopic($chatId, $topicId, $photoUrl, $caption = '', $parseMode = 'Markdown') {
    return telegramRequest('sendPhoto', [
        'chat_id' => $chatId,
        'message_thread_id' => $topicId,
        'photo' => $photoUrl,
        'caption' => $caption,
        'parse_mode' => $parseMode
    ]);
}

// Handler untuk command /start
function handleStart($chatId) {
    $text = "🤖 *Bot Creator Topics Anime*\n\n"
          . "Perintah yang tersedia:\n"
          . "/preview - Lihat data anime dari API\n"
          . "/createtopics - Buat topics di grup ini (jalankan di grup)\n\n"
          . "📌 *Cara Penggunaan:*\n"
          . "1\\. Buat grup baru atau gunakan grup yang ada\n"
          . "2\\. Tambahkan bot ke grup \\& jadikan admin\n"
          . "3\\. Enable 'Topics' di pengaturan grup\n"
          . "4\\. Jalankan /createtopics di grup";
    
    telegramRequest('sendMessage', [
        'chat_id' => $chatId,
        'text' => $text,
        'parse_mode' => 'MarkdownV2'
    ]);
}

// Handler untuk command /preview
function handlePreview($chatId) {
    telegramRequest('sendMessage', [
        'chat_id' => $chatId,
        'text' => '🔄 Mengambil data anime...'
    ]);
    
    $data = getAnimeData();
    
    if (!$data) {
        telegramRequest('sendMessage', [
            'chat_id' => $chatId,
            'text' => '❌ Gagal mengambil data dari API'
        ]);
        return;
    }
    
    $previewText = "📊 Total Anime: " . count($data) . "\n\n";
    
    // Tampilkan 5 anime pertama
    for ($i = 0; $i < min(5, count($data)); $i++) {
        $anime = $data[$i];
        $judul = $anime['judul'] ?? 'Unknown';
        $animeId = $anime['id'] ?? 'N/A';
        $cover = $anime['cover'] ?? 'N/A';
        
        $previewText .= ($i + 1) . ". *" . $judul . "*\n"
                      . "   🆔 ID: `" . $animeId . "`\n"
                      . "   🖼️ Cover: `" . substr($cover, 0, 60) . (strlen($cover) > 60 ? '...' : '') . "`\n\n";
    }
    
    if (count($data) > 5) {
        $previewText .= "... dan " . (count($data) - 5) . " anime lainnya";
    }
    
    telegramRequest('sendMessage', [
        'chat_id' => $chatId,
        'text' => $previewText,
        'parse_mode' => 'Markdown'
    ]);
}

// Handler untuk command /createtopics
function handleCreateTopics($chatId, $chatType) {
    // Cek apakah di grup
    if ($chatType != 'group' && $chatType != 'supergroup') {
        $text = "❌ Command ini hanya bisa digunakan di dalam grup\\!\n\n"
              . "1\\. Tambahkan bot ke grup\n"
              . "2\\. Jadikan bot admin dengan permission 'Manage Topics'\n"
              . "3\\. Enable Forum/Topics di grup\n"
              . "4\\. Jalankan command ini di grup";
        
        telegramRequest('sendMessage', [
            'chat_id' => $chatId,
            'text' => $text,
            'parse_mode' => 'MarkdownV2'
        ]);
        return;
    }
    
    telegramRequest('sendMessage', [
        'chat_id' => $chatId,
        'text' => '🔄 Mengambil data anime...'
    ]);
    
    $animeData = getAnimeData();
    
    if (!$animeData) {
        telegramRequest('sendMessage', [
            'chat_id' => $chatId,
            'text' => '❌ Gagal mengambil data dari API'
        ]);
        return;
    }
    
    telegramRequest('sendMessage', [
        'chat_id' => $chatId,
        'text' => '📊 Ditemukan ' . count($animeData) . ' anime. Membuat topics...'
    ]);
    
    $created = 0;
    $failed = 0;
    $mapping = [];
    
    foreach ($animeData as $index => $anime) {
        $judul = $anime['judul'] ?? 'Unknown';
        $coverUrl = $anime['cover'] ?? '';
        $animeId = $anime['id'] ?? 'N/A';
        
        // Buat topic
        $topicResult = createForumTopic($chatId, $judul);
        
        if (!$topicResult['ok']) {
            $failed++;
            error_log("Gagal buat topic: " . $judul . " - " . json_encode($topicResult));
            
            // Delay lebih lama jika error (rate limit)
            sleep(3);
            continue;
        }
        
        $topicId = $topicResult['result']['message_thread_id'];
        
        // Buat message text
        $messageText = "🎬 *" . $judul . "*\n\n"
                     . "🆔 ID: `" . $animeId . "`\n"
                     . "🔗 Cover URL: " . ($coverUrl ?: 'Tidak tersedia');
        
        // Kirim cover jika ada
        if (!empty($coverUrl)) {
            $photoResult = sendPhotoToTopic($chatId, $topicId, $coverUrl, $messageText);
            
            // Jika gagal kirim foto, kirim text saja
            if (!$photoResult['ok']) {
                sendMessageToTopic($chatId, $topicId, $messageText);
            }
        } else {
            sendMessageToTopic($chatId, $topicId, $messageText);
        }
        
        $created++;
        $mapping[] = [
            'judul' => $judul,
            'topic_id' => $topicId,
            'anime_id' => $animeId
        ];
        
        // Progress update setiap 10 topics
        if ($created % 10 == 0) {
            telegramRequest('sendMessage', [
                'chat_id' => $chatId,
                'text' => '⏳ Progress: ' . $created . '/' . count($animeData) . ' topics dibuat...'
            ]);
        }
        
        // Delay untuk menghindari rate limit (1.5 detik)
        usleep(1500000);
    }
    
    // Simpan mapping ke file
    $filename = 'topics_mapping_' . $chatId . '.json';
    file_put_contents($filename, json_encode([
        'group_id' => $chatId,
        'total_created' => $created,
        'total_failed' => $failed,
        'created_at' => date('Y-m-d H:i:s'),
        'topics' => $mapping
    ], JSON_PRETTY_PRINT));
    
    // Kirim laporan
    $report = "📊 *Laporan Pembuatan Topics*\n\n"
            . "✅ Berhasil: " . $created . "\n"
            . "❌ Gagal: " . $failed . "\n"
            . "📁 Total Data: " . count($animeData) . "\n\n";
    
    if ($failed > 0) {
        $report .= "⚠️ Beberapa topic gagal dibuat \\(mungkin rate limit\\)";
    }
    
    telegramRequest('sendMessage', [
        'chat_id' => $chatId,
        'text' => $report,
        'parse_mode' => 'MarkdownV2'
    ]);
    
    telegramRequest('sendMessage', [
        'chat_id' => $chatId,
        'text' => '💾 Mapping topics tersimpan di file: ' . $filename
    ]);
}

// Main webhook handler
function handleWebhook() {
    $input = file_get_contents('php://input');
    $update = json_decode($input, true);
    
    if (!$update || !isset($update['message'])) {
        http_response_code(200);
        echo 'OK';
        return;
    }
    
    $message = $update['message'];
    $chatId = $message['chat']['id'];
    $chatType = $message['chat']['type'];
    $text = $message['text'] ?? '';
    
    // Parse command
    $command = explode(' ', $text)[0];
    
    switch ($command) {
        case '/start':
            handleStart($chatId);
            break;
            
        case '/preview':
            handlePreview($chatId);
            break;
            
        case '/createtopics':
            handleCreateTopics($chatId, $chatType);
            break;
            
        default:
            // Do nothing
            break;
    }
    
    http_response_code(200);
    echo 'OK';
}

// Polling mode (alternative tanpa webhook)
function runPolling() {
    echo "🤖 Bot started in polling mode...\n";
    
    $offset = 0;
    
    while (true) {
        $updates = telegramRequest('getUpdates', [
            'offset' => $offset,
            'limit' => 10
        ]);
        
        if ($updates['ok'] && !empty($updates['result'])) {
            foreach ($updates['result'] as $update) {
                $offset = $update['update_id'] + 1;
                
                if (!isset($update['message'])) continue;
                
                $message = $update['message'];
                $chatId = $message['chat']['id'];
                $chatType = $message['chat']['type'];
                $text = $message['text'] ?? '';
                
                $command = explode(' ', $text)[0];
                
                switch ($command) {
                    case '/start':
                        handleStart($chatId);
                        break;
                    case '/preview':
                        handlePreview($chatId);
                        break;
                    case '/createtopics':
                        handleCreateTopics($chatId, $chatType);
                        break;
                }
            }
        }
        
        sleep(1);
    }
}

// Mode eksekusi
// Untuk webhook: panggil handleWebhook()
// Untuk polling: panggil runPolling()

// Deteksi mode otomatis
if (php_sapi_name() == 'cli') {
    // Running from command line - use polling
    runPolling();
} else {
    // Running from web server - use webhook
    handleWebhook();
}
?>
