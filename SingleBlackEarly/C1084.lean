import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1084 : checkSingleBlackFast (-9, -5) 26196 .north (-1, -15) (-31, -21) = true := by
  decide +kernel

end LangtonsAnt
