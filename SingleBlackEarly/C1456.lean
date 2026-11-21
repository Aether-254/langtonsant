import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1456 : checkSingleBlackFast (-23, -2) 23164 .north (-1, 6) (-9, -36) = true := by
  decide +kernel

end LangtonsAnt
