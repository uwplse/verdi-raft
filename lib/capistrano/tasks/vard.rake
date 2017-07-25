namespace :vard do

  def vard_cluster
    cluster = roles(:node).collect do |s|
      "-node #{s.properties.name},#{s.properties.host}:#{fetch(:node_port)}"
    end
    cluster.join(' ')
  end

  def vardctl_cluster
    cluster = roles(:node).collect do |s|
      "#{s.properties.host}:#{fetch(:client_port)}"
    end
    cluster.join(',')
  end
  
  desc 'start vard'
  task :start do
    on roles(:node) do |server|
      execute '/sbin/start-stop-daemon',
        '--start',
        '--quiet',
        '--oknodo',
        '--make-pidfile',
        "--pidfile #{current_path}/extraction/vard/tmp/vard.pid",
        '--background',
        "--chdir #{current_path}/extraction/vard",
        '--startas /bin/bash',
        "-- -c 'exec ./vard.native -me #{server.properties.name} -port #{fetch(:client_port)} -dbpath #{current_path}/extraction/vard/tmp #{vard_cluster} > log/vard.log 2>&1'"
    end
  end

  desc 'stop vard'
  task :stop do
    on roles(:node) do
      execute '/sbin/start-stop-daemon', 
        '--stop',
        '--oknodo',
        "--pidfile #{current_path}/extraction/vard/tmp/vard.pid"
    end
  end

  desc 'tail vard log'
  task :tail_log do
    on roles(:node) do
      execute :tail,
        '-n 20',
        "#{shared_path}/extraction/vard/log/vard.log"
    end
  end

  desc 'truncate vard log'
  task :truncate_log do
    on roles(:node) do
      execute :truncate,
        '-s 0',
        "#{shared_path}/extraction/vard/log/vard.log"
    end
  end

  desc 'remove command log'
  task :remove_clog do
    on roles(:node) do
      execute :rm,
        '-f',
        "#{shared_path}/extraction/vard/tmp/clog.bin"
    end
  end

  desc 'remove snapshot'
  task :remove_snapshot do
    on roles(:node) do
      execute :rm,
        '-f',
        "#{shared_path}/extraction/vard/tmp/snapshot.bin"
    end
  end

  desc 'get status'
  task :status do
    run_locally do
      info %x(python2.7 extraction/vard/bench/vardctl.py --cluster #{vardctl_cluster} status)
    end
  end

  desc 'get status remote'
  task :status_remote do
    on roles(:node, name: '0') do |server|
      execute 'python2.7',
        "#{current_path}/extraction/vard/bench/vardctl.py",
        "--cluster #{vardctl_cluster}",
        'status'
    end
  end

  desc 'put key-value pair'
  task :put do
    run_locally do
      info %x(python2.7 extraction/vard/bench/vardctl.py --cluster #{vardctl_cluster} put #{ENV['KEY']} #{ENV['VALUE']})
    end
  end

  desc 'put key-value pair remote'
  task :put_remote do
    on roles(:node, name: '0') do |server|
      execute 'python2.7',
        "#{current_path}/extraction/vard/bench/vardctl.py",
        "--cluster #{vardctl_cluster}",
        'put',
        ENV['KEY'],
        ENV['VALUE']
    end
  end

  desc 'get value for key'
  task :get do
    run_locally do
      info %x(python2.7 extraction/vard/bench/vardctl.py --cluster #{vardctl_cluster} get #{ENV['KEY']})
    end
  end

  desc 'get value for key remote'
  task :get_remote do
    on roles(:node, name: '0') do |server|
      execute 'python2.7',
        "#{current_path}/extraction/vard/bench/vardctl.py",
        "--cluster #{vardctl_cluster}",
        'get',
        ENV['KEY']
    end
  end

end
