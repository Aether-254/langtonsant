import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2171 : checkSingleBlackFast (-90, -64) 14188 .north (34, 26) (-60, -42) = true := by
  decide +kernel

end LangtonsAnt
