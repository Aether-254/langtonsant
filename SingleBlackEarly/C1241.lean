import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1241 : checkSingleBlackFast (12, 18) 12011 .east (-7, -1) (-20, -23) = true := by
  decide +kernel

end LangtonsAnt
