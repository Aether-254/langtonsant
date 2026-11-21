import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0676 : checkSingleBlackFast (16, -10) 7991 .west (-9, 5) (-22, -3) = true := by
  decide +kernel

end LangtonsAnt
