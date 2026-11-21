import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1991 : checkSingleBlackFast (-69, -51) 13048 .north (24, 16) (-50, -32) = true := by
  decide +kernel

end LangtonsAnt
