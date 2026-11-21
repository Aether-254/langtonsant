import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2020 : checkSingleBlackFast (-75, -50) 21687 .east (40, 19) (-6, -58) = true := by
  decide +kernel

end LangtonsAnt
