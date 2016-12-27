namespace :vard do
  
  desc 'start vard'
  task :start do
    cluster = roles(:node).collect { |s| "-node #{s.properties.name},#{s.hostname}:#{fetch(:node_port)}" }
    on roles(:node) do |server|
      execute '/sbin/start-stop-daemon',
        '--start',
        '--quiet',
        '--make-pidfile',
        "--pidfile #{current_path}/extraction/vard/tmp/vard.pid",
        '--background',
        "--chdir #{current_path}/extraction/vard",
        '--startas /bin/bash',
        "-- -c 'exec ./vard.native -me #{server.properties.name} -port #{fetch(:client_port)} -dbpath #{current_path}/extraction/vard/tmp #{cluster.join(' ')} > log/vard.log 2>&1'"
    end
  end

  desc 'stop vard'
  task :stop do
    on roles(:node) do
      execute '/sbin/start-stop-daemon', 
        '--stop',
        "--pidfile #{current_path}/extraction/vard/tmp/vard.pid"
    end
  end

  desc 'tail vard log'
  task :tail_log do
    on roles(:node) do
      execute 'tail',
        '-n 20',
        "#{shared_path}/extraction/vard/log/vard.log"
    end
  end

  desc 'truncate vard log'
  task :truncate_log do
    on roles(:node) do
      execute 'truncate',
        '-s 0',
        "#{shared_path}/extraction/vard/log/vard.log"
    end
  end

end
