import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1954 : checkSingleBlackFast (-69, -44) 21375 .east (37, 16) (-9, -55) = true := by
  decide +kernel

end LangtonsAnt
