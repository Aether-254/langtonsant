import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1204 : checkSingleBlackFast2 (24, 4) 10444 .north (-1, 0) (-25, 2) = true := by
  decide +kernel

end LangtonsAnt
