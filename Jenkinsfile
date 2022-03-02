pipeline {
  agent {
    dockerfile {
      label 'docker'
      additionalBuildArgs '--build-arg USER_ID=$(id -u) --build-arg GROUP_ID=$(id -g)'
    }
  }
  options { ansiColor('xterm') }
  environment {
    COQ_PACKAGE = 'coq-vlsm.dev'
    LONG_REV    = """${sh(returnStdout: true, script: 'git rev-parse HEAD').trim()}"""
  }
  stages {
    stage('Init title') {
      when { changeRequest() }
      steps { script { currentBuild.displayName = "PR ${env.CHANGE_ID}: ${env.CHANGE_TITLE}" } }
    }
    stage('Prepare and Check') {
      stages {
        stage('Prepare') {
          steps {
            sh '''
	      eval $(opam env)
              opam update -y
              opam pin add ${COQ_PACKAGE} . --yes --no-action --kind path
              opam config list
              opam repo list
              opam list
              opam install ${COQ_PACKAGE} --yes -j 8 --deps-only
            '''
          }
        }
        stage('Check') { steps { sh 'eval $(opam env) && opam install ${COQ_PACKAGE} --yes -j 8 --verbose' } }
      }
    }
    stage('Deploy') {
      when {
        branch 'master'
        beforeAgent true
      }
      post { failure { slackSend color: '#cb2431' , channel: '#casper-cbc-internal' , message: "Deploy Phase Failed: ${env.BUILD_URL}" } }
      stages {
        //stage('Deploy Docs') {
        //  steps {
        //    sshagent(['2b3d8d6b-0855-4b59-864a-6b3ddf9c9d1a']) {
        //      sh '''
        //        echo "Trigger Doc Update"
        //      '''
        //    }
        //  }
        //}
        stage('Update Dependents') {
          steps {
            build job: 'DevOps/master', propagate: false, wait: false                                            \
                , parameters: [ booleanParam ( name: 'UPDATE_DEPS'         , value: true                       ) \
                              , string       ( name: 'UPDATE_DEPS_REPO'    , value: 'runtimeverification/vlsm' ) \
                              , string       ( name: 'UPDATE_DEPS_VERSION' , value: "${env.LONG_REV}")           \
                              ]
          }
        }
      }
    }
  }
}
