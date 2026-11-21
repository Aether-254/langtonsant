import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1793 : checkSingleBlackFast (-51, -33) 12112 .north (15, 7) (-41, -23) = true := by
  decide +kernel

end LangtonsAnt
